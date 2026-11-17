#!/usr/bin/env python3
"""Frozen-input whole-CLI measurement with independent semantic/report gates."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import copy
import gzip
import hashlib
import json
import os
import platform
import re
import resource
import signal
import shutil
import statistics
import subprocess
import sys
import time

import loop_report_oracle as report_oracle

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CASES = HERE / 'cases/loop-verification'
MANIFEST = CASES / 'manifest.json'
SNAPSHOT = HERE / 'results/loop-verification-macos-arm64-snapshot.json.gz'
BASE_REV = '0795dd689c40b88d0a0ae37e25bfdc3b06468f8e'
CANDIDATE_REV = '14bb053ca5e09f6036e1a61089452f8ccf90d375'
COMPILER_INPUT_PATHS = ('src', '.cargo', 'Cargo.toml', 'Cargo.lock', 'build.rs',
                        'rust-toolchain', 'rust-toolchain.toml')
CODES = {'verified': 0, 'failed': 5, 'unknown': 6, 'unsupported': 7}
TOOLS = {}
OPTIONS = None
OUTPUT = None


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def capture(args):
    return subprocess.check_output(args, cwd=ROOT, text=True, timeout=10).strip()


def host():
    result = dict(utc=datetime.now(timezone.utc).isoformat(), system=platform.system(),
                  release=platform.release(), machine=platform.machine(), cpus=os.cpu_count(),
                  load_average=os.getloadavg(), python=platform.python_version(),
                  perf_counter=vars(time.get_clock_info('perf_counter')),
                  monotonic=vars(time.get_clock_info('monotonic')))
    commands = {'uptime': ['uptime'],
                'rustc': [shutil.which('rustc') or str(Path.home()/'.cargo/bin/rustc'), '-Vv'],
                'cargo': [shutil.which('cargo') or str(Path.home()/'.cargo/bin/cargo'), '-V'],
                'clang': [shutil.which('clang') or '/usr/bin/clang', '--version'],
                'solver_version': [str(TOOLS['solver'][0]), '-version']}
    if platform.system() == 'Darwin':
        commands['hardware'] = ['sysctl', 'hw.model', 'hw.ncpu', 'hw.physicalcpu', 'hw.memsize']
        commands['cpu_processes'] = ['ps', '-axo', 'pid,pcpu,comm', '-r']
    else:
        commands['hardware'] = ['uname', '-a']
        commands['cpu_processes'] = ['ps', '-eo', 'pid,pcpu,comm', '--sort=-pcpu']
    for name, command in commands.items():
        value = capture(command)
        result[name] = value.splitlines()[:12] if name == 'cpu_processes' else value
    return result


def read_snapshot():
    with gzip.open(SNAPSHOT, 'rt') as stream:
        return json.load(stream)


def check_checkout(directory, expected):
    actual = set()

    def collect(path):
        assert not path.is_symlink(), f'symlink compiler input: {path}'
        name = str(path.relative_to(directory))
        if name in (*COMPILER_INPUT_PATHS[2:], '.cargo/config', '.cargo/config.toml'):
            assert path.is_file(), f'non-regular compiler input: {path}'
        if path.is_dir():
            for child in path.iterdir():
                collect(child)
        else:
            assert path.is_file(), f'non-regular compiler input: {path}'
            actual.add(name)

    for name in COMPILER_INPUT_PATHS:
        path = directory / name
        if path.exists() or path.is_symlink():
            collect(path)
    pinned = {name for name in expected if not name.startswith('tests/')}
    assert actual == pinned, f'compiler input set differs: added={sorted(actual-pinned)}, missing={sorted(pinned-actual)}'
    for name, expected_sha in expected.items():
        path = directory
        for part in Path(name).parts:
            path = path / part
            assert not path.is_symlink(), f'symlink source input: {path}'
        assert path.is_file(), f'missing or non-regular source input: {path}'
        assert sha(path) == expected_sha, f'source checkout differs: {path}'


def identity():
    snapshot = read_snapshot()
    assert snapshot['baseline_revision'] == BASE_REV
    assert snapshot['candidate_revision'] == CANDIDATE_REV
    for variant, revision in [('baseline', BASE_REV), ('candidate', CANDIDATE_REV)]:
        expected = snapshot['source_inputs'][variant]
        names = capture(['git', 'ls-tree', '-r', '--name-only', revision, '--',
                         *COMPILER_INPUT_PATHS]).splitlines()
        assert set(names) == {n for n in expected if not n.startswith('tests/')}, variant
        for name, expected_sha in expected.items():
            actual = digest(subprocess.check_output(['git', 'show', f'{revision}:{name}'], cwd=ROOT, timeout=10))
            assert actual == expected_sha, f'committed source differs: {revision}:{name}'
    check_checkout(OPTIONS.candidate_source, snapshot['source_inputs']['candidate'])
    if OPTIONS.baseline_source is not None:
        check_checkout(OPTIONS.baseline_source, snapshot['source_inputs']['baseline'])
    for name, expected_sha in snapshot['relocation']['public_inputs'].items():
        assert sha(ROOT / name) == expected_sha, f'benchmark input differs: {name}'
    tools = {}
    for name, (path, expected) in TOOLS.items():
        assert sha(path) == expected, f'{name} executable hash differs'
        tools[name] = dict(path=str(path), sha256=expected, bytes=path.stat().st_size)
    return dict(tools=tools, baseline_revision=BASE_REV, candidate_revision=CANDIDATE_REV,
                baseline_source_inputs=snapshot['source_inputs']['baseline'],
                candidate_source_inputs=snapshot['source_inputs']['candidate'],
                baseline_checkout=str(OPTIONS.baseline_source) if OPTIONS.baseline_source else None,
                candidate_checkout=str(OPTIONS.candidate_source),
                identity_mode='new-host' if OPTIONS.new_host else 'recorded-tool-identities',
                snapshot_sha256=sha(SNAPSHOT), harness_inputs=snapshot['relocation']['public_inputs'])


def execute(command):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter_ns()
    child = subprocess.Popen([str(x) for x in command], cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        stdout, stderr = child.communicate(timeout=45)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        stdout, stderr = child.communicate()
        raise AssertionError(f'outer 45-second timeout: {command}; {stderr[-200:]}')
    elapsed = (time.perf_counter_ns() - started) / 1_000_000
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return dict(command=list(map(str, command)), exit=child.returncode, stdout=stdout, stderr=stderr,
                elapsed_ms=elapsed, user_cpu_ms=(after.ru_utime-before.ru_utime)*1000,
                system_cpu_ms=(after.ru_stime-before.ru_stime)*1000)


def normalize(report):
    result = copy.deepcopy(report)
    if result['compiler']:
        for key in ['executable', 'executable_path_bytes_hex', 'sha256']:
            result['compiler'][key] = '<compiler identity>'
    for query in result['obligations']:
        query['query'] = re.sub(r'\(set-option :timeout [0-9]+\)',
                                '(set-option :timeout REMAINING)', query['query'])
        query['query_sha256'] = digest(query['query'].encode())
    return result


def unknown_prefix(report):
    assert len(report['expansions']) == 1 and report['expansions'][0]['source_function_id'] == 0
    assert len(report['loop_occurrences']) == 45
    assert all(not o['head_symbols'] and o['source_function_id']==0 and o['expansion_id']==0 for o in report['loop_occurrences'])
    expected=['precondition_satisfiable','body_safe']+['loop_invariant_initialized','loop_invariant_preserved']*45
    assert [q['kind'] for q in report['obligations']] == expected[:35]
    identifiers=[]
    for q in report['obligations']:
        definitions,declarations,assertion,requests=report_oracle.rendered(q)
        assert assertion==q['query_assertion'] and not declarations and not requests
        assert not report_oracle.dependencies(definitions,assertion) and q['model_symbols']==[]
        if q['kind']=='precondition_satisfiable':
            assert q['checks']==[] and q['model']=={'replayed':False,'assignments':[]}
            continue
        implication_ids=[]
        for check in q['checks']:
            identifiers.append(check['id']);implication_ids.append(check['implication'])
            assert definitions[check['implication']]==['=>',check['guard'],check['required']]
            assert check['source_function_id']==0 and check['expansion_id']==0
            origin=check['origin'];assert origin['kind']==q['kind'] and origin['clause_index']==0
            occurrence=report['loop_occurrences'][origin['occurrence_id']]
            assert origin['loop_node_id']==occurrence['loop_node_id']
            loop=next(l for l in report['functions'][0]['loops'] if l['node_id']==origin['loop_node_id'])
            assert q['location']==loop['clauses'][0]['location']
        top=definitions[assertion];assert top[0]=='not'
        assert report_oracle.conjunction_members(definitions,top[1])==implication_ids
    assert identifiers==list(range(33))
    assert report['obligations'][-1]['checks'][0]['origin']['occurrence_id']==16


def validate(row, case, variant):
    report = json.loads(row['stdout'])
    path = CASES / case['file']
    loop = case['route'] == 'loop'
    status = 'unsupported' if loop and variant == 'baseline' else case['status']
    assert not row['stderr']
    assert row['exit'] == CODES[status] and report['status'] == status, (case['name'], variant, report.get('message'))
    assert report['type_checked'] is True and report['trust'] == 'smt-trusted'
    assert report['scope']['termination_proved'] is False and report['scope']['native_correctness'] is False
    assert len(report['sources']) == 1
    source = report['sources'][0]
    assert source['path'] == str(path) and source['sha256'] == case['source_sha256'] == sha(path)
    assert source['bytes'] == path.stat().st_size
    pure = case['route'] == 'pure'
    assert report['schema'] == ('apl-verify-v0' if pure else 'apl-verify-v1')
    assert report['semantic_revision'] == ('m1-2026-11-16' if pure else 'local-state-2026-11-17')
    if pure:
        assert 'verification_revision' not in report
    else:
        assert report['verification_revision'] == ('apl-loop-verify-v1' if loop and variant == 'candidate' else 'apl-state-verify-v1')
    queries = report['obligations']
    if status == 'unsupported':
        assert not queries and report['compiler'] is None and report['solver'] is None
        assert report['expanded_nodes'] == 0
        if variant == 'candidate':
            assert report['source_loop_metadata_complete'] is False
            assert not report['expansions'] and not report['loop_occurrences']
            assert all(f['loops'] is None and f['bindings'] is None and f['invariant_clauses'] is None for f in report['functions'])
    else:
        assert report['compiler']['sha256'] == TOOLS[variant][1]
        assert report['solver']['sha256'] == TOOLS['solver'][1]
        assert len(queries) == case['queries'], (case['name'], len(queries))
        for index, query in enumerate(queries):
            assert query['id'] == index and query['query_complete'] is True
            assert query['query_sha256'] == digest(query['query'].encode())
            assert query['solver_status'] in ('sat', 'unsat') and query['status'] in ('verified', 'failed')
            assert query['expected_solver_status'] == ('sat' if query['kind'] == 'precondition_satisfiable' else 'unsat')
            assert query['status'] == ('verified' if query['solver_status'] == query['expected_solver_status'] else 'failed')
            if query['solver_status'] == 'sat':
                assert isinstance(query['model'], dict) and query['model']['replayed'] is False
            else:
                assert query['model'] is None
            if not loop:
                function = report['functions'][query['function_id']]
                expected = [(i, f'p{i}', t) for i, t in enumerate(function['parameter_types']) if t != 'unit']
                if not pure:
                    assert query['model_symbols'] == [dict(symbol=s, type=t, origin=dict(kind='parameter', index=i)) for i,s,t in expected]
                if query['model']:
                    values = query['model']['assignments']
                    assert [(a['parameter'], a['symbol'], a['type']) for a in values] == expected
                    for a in values:
                        assert type(a['value']) is bool if a['type']=='bool' else isinstance(a['value'], str) and -(2**63)<=int(a['value'])<2**63
        if status == 'verified':
            assert all(q['status'] == 'verified' for q in queries)
        if status == 'failed':
            assert [q['kind'] for q in queries if q['status'] == 'failed'] == [case['failed_kind']]
        if loop:
            assert report['source_loop_metadata_complete'] is True
            if status == 'unknown':
                assert report['message'] == case['expected_message']
                assert all(q['function'] == case['completed_function'] and q['status'] == 'verified' for q in queries)
                assert all(not o['head_symbols'] for o in report['loop_occurrences'])
                unknown_prefix(report)
            else:
                oracle = report_oracle.check_report(report)
                assert oracle['heads'] == case['heads'] and oracle['occurrences'] == case['occurrences']
    metrics = dict(status=status, query_count=len(queries), query_bytes=sum(len(q['query'].encode()) for q in queries),
                   expanded_nodes=report.get('expanded_nodes', 0), functions=len(report['functions']),
                   heads=sum(len(o['head_symbols']) for o in report.get('loop_occurrences', [])),
                   occurrences=len(report.get('loop_occurrences', [])))
    return report, metrics


def verify(case, variant):
    row = execute([TOOLS[variant][0], 'verify', CASES/case['file'], '--json',
                   '--solver', TOOLS['solver'][0], '--timeout-ms', '30000'])
    try:
        report, row['metrics'] = validate(row, case, variant)
    except Exception:
        (OUTPUT/f'rejected-{case["name"]}-{variant}.json').write_text(json.dumps(row,indent=2)+'\n')
        raise
    row.update(case=case['name'], variant=variant, normalized_report_sha256=digest(json.dumps(normalize(report), sort_keys=True).encode()))
    return row


def runtime_gates(cases):
    results = []
    directory = OUTPUT/'runtime'; directory.mkdir(exist_ok=True)
    for case in cases:
        original = CASES/case['file']
        if case['category']=='common':
            probes = [(args, str(value), None) for args,value in case.get('eval', [])]
            if case.get('trap'): probes.append(('', None, 'arithmetic_overflow'))
            for index, (arguments, value, trap) in enumerate(probes):
                path = directory/f'{case["name"]}-{index}.apl'
                path.write_text(original.read_text()+f'\nfn main()->i64{{f({arguments})}}\n')
                for variant in ['baseline','candidate']:
                    row=execute([TOOLS[variant][0],'eval',path])
                    assert (row['exit']==2 and trap in row['stderr']) if trap else (row['exit']==0 and row['stdout']==value+'\n' and not row['stderr'])
                    row.update(case=case['name'],variant=variant,source_sha256=sha(path)); results.append(row)
        elif case['category']=='loop':
            row=execute([TOOLS['candidate'][0],'check',original]);assert row['exit']==0;results.append(row)
            args=[TOOLS['candidate'][0],'eval',original]
            outcome=case.get('bounded_evaluator_outcome')
            if outcome=='resource_limit':args += ['--fuel','1000']
            row=execute(args)
            if case.get('finite_value') is not None:assert row['exit']==0 and row['stdout']==case['finite_value']+'\n'
            elif outcome=='resource_limit':assert row['exit']==3 and 'resource_limit' in row['stderr']
            else:assert row['exit']==2 and outcome in row['stderr']
            results.append(row)
            if case.get('finite_value') is not None:
                native=directory/(case['name']+'-native')
                row=execute([TOOLS['candidate'][0],'build',original,'-o',native]);assert row['exit']==0;results.append(row)
                row=execute([native]);assert row['exit']==0 and row['stdout']==case['finite_value']+'\n';results.append(row)
    return results


def sensitivity(row, case):
    base=json.loads(row['stdout']); mutations={}
    for name in ['status','query_hash','complete','sat_model','manifest','guard']:
        altered=copy.deepcopy(base)
        q=next(q for q in altered['obligations'] if q['kind']=='loop_invariant_initialized')
        if name=='status':altered['status']='failed'
        elif name=='query_hash':q['query_sha256']='0'*64
        elif name=='complete':q['query_complete']=False
        elif name=='sat_model':next(q for q in altered['obligations'] if q['solver_status']=='sat')['model']=None
        elif name=='manifest':next(q for q in altered['obligations'] if any(s['origin']['kind']=='loop_head' for s in q['model_symbols']))['model_symbols']=[]
        else:q['checks'][0]['guard']='n999999'
        changed=dict(row,stdout=json.dumps(altered))
        try:validate(changed,case,'candidate')
        except (AssertionError,KeyError,TypeError):mutations[name]='rejected'
        else:raise AssertionError(f'gate accepted {name}')
    return mutations


def save(path, data):
    with gzip.open(path,'wt') as f:json.dump(data,f,indent=2)


def summarize(rows):
    return {key:dict(count=len(rows),median=statistics.median(r[key] for r in rows),minimum=min(r[key] for r in rows),maximum=max(r[key] for r in rows))
            for key in ['elapsed_ms','user_cpu_ms','system_cpu_ms']}


def configure():
    global OPTIONS, TOOLS, OUTPUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['gate', 'time'])
    for name in ['baseline', 'candidate', 'solver']:
        parser.add_argument('--'+name, type=Path, required=True, help='explicit executable path')
        parser.add_argument('--'+name+'-sha256', help='required with --new-host; otherwise recorded hash is mandatory')
    parser.add_argument('--output-dir', type=Path, required=True, help='fresh directory for gate; same directory for time')
    parser.add_argument('--candidate-source', type=Path, default=ROOT, help='checkout matching the pinned candidate source')
    parser.add_argument('--baseline-source', type=Path, help='checkout matching the pinned baseline; required with --new-host')
    parser.add_argument('--new-host', action='store_true', help='record new executable identities, never relabel historical timings')
    OPTIONS = parser.parse_args()
    if not __debug__:
        parser.error('assertion gates require Python without -O or PYTHONOPTIMIZE')
    if os.name != 'posix':
        parser.error('POSIX process groups and child resource accounting are required')
    if OPTIONS.new_host and OPTIONS.baseline_source is None:
        parser.error('--new-host requires --baseline-source')
    snapshot = read_snapshot()
    for name in ['baseline', 'candidate', 'solver']:
        explicit = getattr(OPTIONS, name+'_sha256')
        recorded = snapshot['recorded_tools'][name]['sha256']
        if OPTIONS.new_host:
            if explicit is None or not re.fullmatch(r'[0-9a-f]{64}', explicit):
                parser.error('--new-host requires an explicit lowercase SHA-256 for every executable')
        elif explicit is not None and explicit != recorded:
            parser.error('different executable identities require --new-host')
        TOOLS[name] = (getattr(OPTIONS, name).resolve(), explicit or recorded)
    OPTIONS.candidate_source = OPTIONS.candidate_source.resolve()
    if OPTIONS.baseline_source is not None:
        OPTIONS.baseline_source = OPTIONS.baseline_source.resolve()
    OUTPUT = OPTIONS.output_dir.resolve()
    # Identity failures occur before any measured or runtime command.
    identity()
    if OPTIONS.mode == 'gate':
        OUTPUT.mkdir(parents=True, exist_ok=False)
    else:
        if not (OUTPUT/'freeze.json').is_file() or (OUTPUT/'raw.json.gz').exists():
            parser.error('time requires accepted gates and an output directory with no raw.json.gz')


def main():
    configure()
    mode=OPTIONS.mode
    cases=json.loads(MANIFEST.read_text())
    run=dict(schema='apl-loop-verification-measurement-v1',mode=mode,status='running',host_before=host(),identity_before=identity(),rows=[])
    output=OUTPUT/('gates.json.gz' if mode=='gate' else 'raw.json.gz')
    try:
        if mode=='gate':
            for case in cases:
                pair=[verify(case,v) for v in ['baseline','candidate']]
                if case['category']=='common':assert pair[0]['normalized_report_sha256']==pair[1]['normalized_report_sha256'],case['name']
                run['rows'].extend(pair)
                print(json.dumps(dict(gated=case['name'],outcomes=[r['metrics'] for r in pair])),flush=True)
            run['runtime_checks']=runtime_gates(cases)
            counter=next(r for r in run['rows'] if r['case']=='counter' and r['variant']=='candidate')
            run['gate_sensitivity']=sensitivity(counter,next(c for c in cases if c['name']=='counter'))
        else:
            freeze=json.loads((OUTPUT/'freeze.json').read_text())
            assert run['identity_before']==freeze['identity']
            assert sha(OUTPUT/'gates.json.gz')==freeze['gates_sha256']
            run['freeze_sha256']=sha(OUTPUT/'freeze.json')
            for round_number in range(6):
                order=cases if round_number%2==0 else list(reversed(cases))
                variants=['baseline','candidate'] if round_number%2==0 else ['candidate','baseline']
                for case in order:
                    pair=[]
                    for variant in variants:
                        row=verify(case,variant);row.update(round=round_number,phase='warmup' if round_number==0 else 'sample')
                        expected=freeze['gates'][case['name']][variant]
                        assert row['normalized_report_sha256']==expected['normalized_report_sha256'],(case['name'],variant)
                        assert {k:v for k,v in row['metrics'].items() if k!='query_bytes'}=={k:v for k,v in expected['metrics'].items() if k!='query_bytes'}
                        pair.append(row);run['rows'].append(row)
                    if case['category']=='common':assert pair[0]['normalized_report_sha256']==pair[1]['normalized_report_sha256']
                print(json.dumps(dict(round=round_number,phase='warmup' if round_number==0 else 'sample',commands=len(run['rows']),load=os.getloadavg())),flush=True)
            run['summaries']=[dict(case=c['name'],category=c['category'],variant=v,
                                   timing=summarize([r for r in run['rows'] if r['case']==c['name'] and r['variant']==v and r['phase']=='sample']),
                                   metrics=freeze['gates'][c['name']][v]['metrics']) for c in cases for v in ['baseline','candidate']]
        run['identity_after']=identity();assert run['identity_before']==run['identity_after']
        run['host_after']=host();run['status']='accepted';run['unexpected_failures']=0
    except Exception as error:
        run.update(status='rejected',unexpected_failures=1,error=repr(error))
        raise
    finally:
        save(output,run)
    if mode=='gate':
        freeze=dict(identity=run['identity_before'],gates_sha256=sha(output),gates={c['name']:{v:{k:r[k] for k in ['metrics','normalized_report_sha256']}
                     for v in ['baseline','candidate'] for r in run['rows'] if r['case']==c['name'] and r['variant']==v} for c in cases})
        (OUTPUT/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
    print(json.dumps(dict(status=run['status'],output=str(output),sha256=sha(output),commands=len(run['rows']))),flush=True)


if __name__=='__main__':
    main()
