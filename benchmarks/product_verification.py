#!/usr/bin/env python3
"""Replay the frozen ANL tuple-verification corpus and paired CLI measurements."""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
import platform
import resource
import signal
import statistics
import subprocess
import sys
import time

sys.dont_write_bytecode = True
BENCH = Path(__file__).resolve().parent
REPO = BENCH.parent
HERE = BENCH / 'cases/product-verification'
RESULTS = BENCH / 'results'
ARTIFACTS = RESULTS / 'product-verification-artifacts.json'
COMPILER_INPUTS = ('src', '.cargo', 'Cargo.toml', 'Cargo.lock', 'build.rs',
                   'rust-toolchain', 'rust-toolchain.toml')
ENV_KEYS = ('PATH', 'RUSTUP_TOOLCHAIN', 'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS',
            'SDKROOT', 'CPATH', 'C_INCLUDE_PATH', 'LIBRARY_PATH',
            'MACOSX_DEPLOYMENT_TARGET', 'DYLD_LIBRARY_PATH',
            'DYLD_INSERT_LIBRARIES', 'OMP_NUM_THREADS')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def audit():
    inventory = json.loads(ARTIFACTS.read_text())
    for name, digest in inventory['inputs'].items():
        path = BENCH / name
        need(path.is_file() and not path.is_symlink() and sha(path) == digest,
             'benchmark input differs: ' + name)
    actual = {str(p.relative_to(BENCH)) for p in HERE.rglob('*') if p.is_file()}
    expected = {n for n in inventory['inputs'] if n.startswith('cases/product-verification/')}
    need(actual == expected, 'fixture inventory differs')
    spec = importlib.util.spec_from_file_location('product_report_oracle', BENCH / 'product_report_oracle.py')
    gate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gate)
    gate.raw_digest_selfcheck()
    need(not gate.same(True, 1) and not gate.same(1, 1.0), 'JSON types were coerced')
    for text in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
        try:
            gate.strict(text)
        except (gate.Failure, ValueError):
            pass
        else:
            raise RuntimeError('invalid JSON accepted')
    manifest = gate.strict((HERE / 'manifest.json').read_bytes())
    need(manifest['warmups'] == 2 and manifest['samples'] == 7, 'round counts differ')
    names = [r['name'] for r in manifest['cases']]
    need(len(names) == len(set(names)) == 33, 'case inventory differs')
    for row in manifest['cases']:
        need(sha(HERE / row['file']) == row['source_sha256'], 'source manifest differs')
    schedule = manifest['scalar_pair_schedule']
    need({r['case'] for r in schedule} == {r['name'] for r in manifest['cases'] if r['group'] == 'scalar'},
         'pair schedule differs')
    need(len(schedule) == 12, 'scalar schedule count differs')
    need(sum(r['samples'].count('AB') for r in schedule) == 42 and
         sum(r['samples'].count('BA') for r in schedule) == 42, 'unbalanced pair schedule')
    for row in schedule:
        need(row['warmups'] == ['AB', 'BA'] and len(row['samples']) == 7 and
             abs(row['samples'].count('AB') - row['samples'].count('BA')) == 1,
             'per-case schedule differs')
    return manifest, gate


def check_source(root, expected):
    actual = set()

    def collect(path):
        need(not path.is_symlink(), 'symlink source input: ' + str(path))
        if path.is_dir():
            for child in path.iterdir():
                collect(child)
        else:
            need(path.is_file(), 'nonregular source input: ' + str(path))
            actual.add(str(path.relative_to(root)))

    for name in COMPILER_INPUTS:
        path = root / name
        if path.exists() or path.is_symlink():
            collect(path)
    need(actual == set(expected), 'compiler source/configuration inventory differs: ' + str(root))
    for name, digest in expected.items():
        need(sha(root / name) == digest, 'compiler source differs: ' + name)


def tool_version(path, flag):
    result = subprocess.run([str(path), flag], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    need(result.returncode == 0 and not result.stderr, 'tool version command failed: ' + str(path))
    return result.stdout.decode().strip()


def identity(args):
    bindings = json.loads((RESULTS / 'product-verification-sources.json').read_text())
    tools = {}
    for side in ('baseline', 'candidate'):
        source = bindings['source_inputs'][side]
        root = getattr(args, side + '_source').resolve()
        check_source(root, source['files'])
        binary = getattr(args, side).resolve()
        expected = getattr(args, side + '_sha256') if args.new_host else source['release_binary_sha256']
        need(expected and sha(binary) == expected, side + ' executable identity differs')
        tools[side] = dict(path=str(binary), sha256=expected, source_root=str(root),
                           source_tree_sha256=source['source_tree_sha256'], revision=source['revision'])
    expected_solver = args.solver_sha256 if args.new_host else bindings['tools']['solver']['sha256']
    need(expected_solver and sha(args.solver) == expected_solver, 'solver executable identity differs')
    if not hasattr(args, 'versions'):
        args.versions = dict(rustc=tool_version(args.rustc, '-Vv'), cargo=tool_version(args.cargo, '-Vv'),
                             solver=tool_version(args.solver, '-version'))
    need(args.versions['rustc'].startswith('rustc 1.99.1 ') and
         args.versions['cargo'].startswith('cargo 1.99.1 ') and
         args.versions['solver'].startswith('Z3 version 5.3.3 '), 'pinned tool version differs')
    for name in ('rustc', 'cargo', 'solver'):
        path = getattr(args, name).resolve()
        need(path.name != 'rustup', 'pass the real toolchain executable, not a rustup proxy: ' + name)
        if not args.new_host:
            need(sha(path) == bindings['tools'][name]['sha256'], 'historical tool identity differs: ' + name)
        tools[name] = dict(path=str(path), sha256=sha(path), version=args.versions[name])
    python = Path(sys.executable).resolve()
    tools['python'] = dict(path=str(python), sha256=sha(python), version=platform.python_version())
    return dict(schema='anl-product-verification-run-identity-v1', new_host=args.new_host,
                tools=tools, input_manifest_sha256=sha(ARTIFACTS),
                host=dict(system=platform.system(), release=platform.release(), machine=platform.machine(),
                          logical_cpus=os.cpu_count()), environment={k: os.environ.get(k) for k in ENV_KEYS})


def verify(binary, row, solver, directory, measured=False):
    return execute([binary, 'verify', HERE / row['file'], '--solver', solver,
                    '--timeout-ms', '30000', '--json'], directory, measured)

def execute(argv,directory,measured=False,timeout=45):
    """Adapted from public flat_products.execute; immediate child wait4, no cumulative maxrss."""
    directory.mkdir(parents=True,exist_ok=False);out=directory/'stdout';err=directory/'stderr';child=None;expired=False
    def expire(signum,frame):
        nonlocal expired
        expired=True
        if child is not None:
            try:os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError:pass
    def bounds():
        resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024*1024,64*1024*1024));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    old=signal.signal(signal.SIGALRM,expire)
    try:
        with out.open('wb') as stdout,err.open('wb') as stderr:
            signal.setitimer(signal.ITIMER_REAL,timeout)
            start=time.perf_counter_ns() if measured else None
            child=subprocess.Popen([str(a) for a in argv],cwd=REPO,env=os.environ.copy(),stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=bounds)
            _,status,usage=os.wait4(child.pid,0)
            wall=time.perf_counter_ns()-start if measured else None;child.returncode=os.waitstatus_to_exitcode(status)
    except BaseException:
        if child is not None and child.returncode is None:
            try:os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            try:_,status,_=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
            except ChildProcessError:pass
        raise
    finally:signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old)
    result=subprocess.CompletedProcess(argv,child.returncode,out.read_bytes(),err.read_bytes())
    record=dict(argv=[str(a) for a in argv],cwd=str(REPO),exit=child.returncode,timeout=expired,stdout_sha256=sha(out),stderr_sha256=sha(err),stdout_bytes=out.stat().st_size,stderr_bytes=err.stat().st_size)
    if measured:
        record.update(wall_ns=wall,user_cpu_ns=round(usage.ru_utime*1e9),system_cpu_ns=round(usage.ru_stime*1e9),cpu_ns=round((usage.ru_utime+usage.ru_stime)*1e9),peak_rss_bytes=int(usage.ru_maxrss)*(1 if platform.system()=='Darwin' else 1024),
            wait4_raw={name:getattr(usage,name) for name in dir(usage) if name.startswith('ru_')},rss_semantics='wait4 reaped process maximum; not simultaneous summed process-tree RSS',rss_native_unit='bytes' if platform.system()=='Darwin' else 'KiB')
    save(directory/'command.json',record)
    need(not expired,'process timeout; raw result retained at '+str(directory))
    return result,record

def work(report,stdout):
    obligations=report['obligations'];functions=report.get('functions',[])
    return dict(status=report['status'],message=report.get('message'),expanded_nodes=report.get('expanded_nodes'),resources=report.get('resources'),
        reported_bindings=sum(len(f.get('bindings',[])) for f in functions),parameter_leaf_slots=sum(sum(len(t['tuple']) if isinstance(t,dict) else 1 for t in f.get('parameter_types',[])) for f in functions),
        loop_occurrences=len(report.get('loop_occurrences',[])),expansions=len(report.get('expansions',[])),
        allocated_heads=sum(len(o.get('head_symbols',[])) for o in report.get('loop_occurrences',[])),named_checks_completed=sum(len(q.get('checks',[])) for q in obligations),executed_analysis_fields=None,
        queries=len(obligations),query_bytes=sum(len(q['query'].encode()) for q in obligations),report_bytes=len(stdout),
        accounting_note='Null means absent in the public report; no private counters or inferred zeroes.')

def accept(gate,result,row,binary_sha,solver_sha,final_scope=None):
    report=gate.check_report(result,row,product=row['group']!='scalar')
    need(not result.stderr,row['name']+' successful report wrote stderr')
    need(report['compiler']['sha256']==binary_sha,'reported compiler identity differs')
    need(report['solver']['sha256']==solver_sha,'reported solver identity differs')
    need(len(report['sources'])==1 and report['sources'][0]['sha256']==row['source_sha256'],'reported source identity differs')
    if final_scope is not None and row['group']!='scalar':need(gate.same(report['scope'],final_scope),'final proof scope differs')
    return report

def runtime(gate,binary,row,directory,original):
    expected=row['runtime'];source=HERE/(row['file'] if original else expected['file'])
    ev,_=execute([binary,'eval',source,'--fuel','100000'],directory/'eval')
    need(ev.returncode==expected['exit'],'runtime exit differs')
    if 'stdout' in expected:need(ev.stdout.decode()==expected['stdout'] and not ev.stderr,'runtime value differs')
    else:need(expected['diagnostic'] in ev.stderr.decode(),'runtime trap differs')
    core,_=execute([binary,'dump-core',source],directory/'dump-core');need(core.returncode==0 and not core.stderr,'core generation rejected');gate.strict(core.stdout)
    path=directory/'program.json';path.write_bytes(core.stdout)
    wire,_=execute([binary,'eval-core',path,'--fuel','100000'],directory/'eval-core')
    need(wire.returncode==expected['exit'],'typed runtime exit differs')
    need(gate.same(gate.strict(wire.stdout),expected['typed']),'typed runtime result differs')
    return core.stdout

def environment_context():
    value=dict(load_average=os.getloadavg(),logical_cpus=os.cpu_count(),platform=platform.platform())
    for key,argv in [('processes',['ps','-axo','pid,ppid,pcpu,pmem,comm']),('power',['pmset','-g','batt']),('thermal',['pmset','-g','therm'])]:
        try:
            r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5);value[key]=dict(argv=argv,exit=r.returncode,stdout=r.stdout.decode(errors='replace'),stderr=r.stderr.decode(errors='replace'))
        except (OSError,subprocess.TimeoutExpired) as error:value[key]=dict(unavailable=str(error))
    return value

def summarize(records):
    rows=[]
    for name in sorted({r['case'] for r in records}):
        items=[r for r in records if r['case']==name and not r['warmup']];row=dict(case=name,verdict='inconclusive; limiter profiling and variation review pending',metrics={})
        for metric in ('wall_ns','cpu_ns','peak_rss_bytes'):
            stat={side:dict(median=statistics.median([r[metric] for r in items if r['side']==side]),min=min(r[metric] for r in items if r['side']==side),max=max(r[metric] for r in items if r['side']==side)) for side in sorted({r['side'] for r in items})}
            if 'baseline' in stat:
                ratios=[next(r[metric] for r in items if r['pair']==i and r['side']=='candidate')/next(r[metric] for r in items if r['pair']==i and r['side']=='baseline') for i in range(7)]
                ratio=statistics.median(ratios);stat['paired_ratios']=ratios;stat['median_paired_ratio']=ratio;stat['investigate']=abs(ratio-1)>(.15 if metric=='peak_rss_bytes' else .10)
            row['metrics'][metric]=stat
        rows.append(row)
    return rows


def accounting(gate, directory):
    fixture = BENCH / 'product_accounting_fixture.py'
    result, record = execute([sys.executable, fixture], directory, measured=True, timeout=10)
    parent = gate.strict(result.stdout)
    child = gate.strict(parent['child_stdout'])
    waited = parent['child_wait4']['ru_utime'] + parent['child_wait4']['ru_stime']
    top = record['wait4_raw']['ru_utime'] + record['wait4_raw']['ru_stime']
    self_cpu = parent['parent_self_usage']['ru_utime'] + parent['parent_self_usage']['ru_stime']
    included = top >= waited * .95 and top > self_cpu + waited * .8
    passed = (result.returncode == 0 and parent['child_exit'] == 0 and not result.stderr and
              not parent['child_stderr'] and included and child['intended_allocation_bytes'] == 24 * 1024 * 1024)
    value = dict(result='PASS' if passed else 'FAIL', classification='synthetic accounting, not language performance',
                 waited_descendant_cpu_included=included, fixture_sha256=sha(fixture),
                 record=record, parent=parent, child=child,
                 limitation='One waited child only. RSS is a kernel high-water statistic, not simultaneous summed tree RSS.')
    save(directory / 'validation.json', value)
    need(passed, 'wait4 child accounting failed; evidence retained')


def preflight(args):
    manifest, gate = audit()
    ident = identity(args)
    args.out.mkdir(parents=True, exist_ok=False)
    directory = args.out / 'gate'
    directory.mkdir()
    save(directory / 'identity.json', ident)
    accounting(gate, directory / 'accounting')
    scope = gate.strict((HERE / 'scope.json').read_bytes())
    rows = []
    for case in manifest['cases']:
        row = dict(case=case['name'], group=case['group'], passed=False)
        try:
            baseline_report = None
            if case['group'] == 'scalar':
                result, _ = verify(args.baseline, case, args.solver, directory / case['name'] / 'baseline/verify')
                baseline_report = accept(gate, result, case, ident['tools']['baseline']['sha256'], ident['tools']['solver']['sha256'])
                row['baseline'] = work(baseline_report, result.stdout)
            result, _ = verify(args.candidate, case, args.solver, directory / case['name'] / 'candidate/verify')
            report = accept(gate, result, case, ident['tools']['candidate']['sha256'], ident['tools']['solver']['sha256'], scope)
            row['candidate'] = work(report, result.stdout)
            if baseline_report is not None:
                need(gate.same(gate.normalize(baseline_report), gate.normalize(report)), 'complete scalar reports differ')
            for side, binary, original in [('baseline', args.baseline, False), ('candidate', args.candidate, True)]:
                core = runtime(gate, binary, case, directory / case['name'] / side / 'runtime', original)
                if side == 'baseline':
                    baseline_core = core
                else:
                    need(core == baseline_core, 'annotation erasure changed core bytes')
            row['passed'] = True
        except Exception as error:
            row['error'] = str(error)
        rows.append(row)
        save(directory / 'summary.json', dict(result='PASS' if all(r['passed'] for r in rows) else 'FAIL',
                                              complete=len(rows) == len(manifest['cases']), rows=rows))
        print(json.dumps(row), flush=True)
    audit()
    need(gate.same(identity(args), ident), 'identity changed during preflight')
    save(directory / 'evidence.json', dict(files={str(p.relative_to(directory)): sha(p)
                                                 for p in sorted(directory.rglob('*')) if p.is_file()}))
    need(all(r['passed'] for r in rows), 'semantic preflight failed; every attempted case retained')


def validate_preflight(args, gate):
    directory = args.out / 'gate'
    summary = gate.strict((directory / 'summary.json').read_bytes())
    need(summary['result'] == 'PASS' and summary['complete'] is True, 'complete successful gate required')
    expected = gate.strict((HERE / 'manifest.json').read_bytes())['cases']
    need([r['case'] for r in summary['rows']] == [r['name'] for r in expected] and
         all(r['passed'] is True for r in summary['rows']), 'complete preflight case inventory required')
    ident = identity(args)
    need(gate.same(gate.strict((directory / 'identity.json').read_bytes()), ident), 'preflight identity differs')
    for name, digest in gate.strict((directory / 'evidence.json').read_bytes())['files'].items():
        need(sha(directory / name) == digest, 'preflight evidence differs: ' + name)
    evidence = gate.strict((directory / 'evidence.json').read_bytes())['files']
    actual = {str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and p.name != 'evidence.json'}
    need(set(evidence) == actual, 'preflight evidence inventory differs')
    check = gate.strict((directory / 'accounting/validation.json').read_bytes())
    need(check['result'] == 'PASS' and check['waited_descendant_cpu_included'] is True, 'accounting check required')
    return ident


def measure(args):
    manifest, gate = audit()
    ident = validate_preflight(args, gate)
    directory = args.out / 'measure'
    directory.mkdir(exist_ok=False)
    save(directory / 'identity.json', ident)
    save(directory / 'environment-before.json', environment_context())
    scope = gate.strict((HERE / 'scope.json').read_bytes())
    schedules = {r['case']: r for r in manifest['scalar_pair_schedule']}
    records = []
    for row in manifest['cases']:
        if row['group'] not in ('scalar', 'product'):
            continue
        plan = schedules[row['name']] if row['group'] == 'scalar' else dict(warmups=['B'] * 2, samples=['B'] * 7)
        for phase in ('warmups', 'samples'):
            for pair, order in enumerate(plan[phase]):
                reports = {}
                for letter in order:
                    side = 'baseline' if letter == 'A' else 'candidate'
                    result, record = verify(getattr(args, side), row, args.solver,
                                            directory / row['name'] / phase / str(pair) / side, measured=True)
                    record.update(case=row['name'], group=row['group'], side=side, pair=pair,
                                  order=order, warmup=phase == 'warmups', passed=False)
                    records.append(record)
                    save(directory / 'samples.json', records)
                    try:
                        report = accept(gate, result, row, ident['tools'][side]['sha256'],
                                        ident['tools']['solver']['sha256'], scope)
                        record['work'] = work(report, result.stdout)
                        reference = args.out / 'gate' / row['name'] / side / 'verify/stdout'
                        need(gate.same(gate.normalize(report), gate.normalize(gate.strict(reference.read_bytes()))),
                             'sample report differs from preflight')
                        reports[side] = report
                        record['passed'] = True
                    except Exception as error:
                        record['error'] = str(error)
                        save(directory / 'samples.json', records)
                        raise
                    save(directory / 'samples.json', records)
                if len(reports) == 2:
                    need(gate.same(gate.normalize(reports['baseline']), gate.normalize(reports['candidate'])),
                         'paired scalar reports differ')
                audit()
                validate_preflight(args, gate)
    audit()
    validate_preflight(args, gate)
    save(directory / 'environment-after.json', environment_context())
    save(directory / 'summary.json', summarize(records))
    save(directory / 'evidence.json', dict(files={str(p.relative_to(directory)): sha(p)
                                                 for p in sorted(directory.rglob('*')) if p.is_file()}))


def read_archive(name, inventory, gate):
    path = RESULTS / name
    need(sha(path) == inventory['archives'][name]['sha256'], 'archive digest differs: ' + name)
    with gzip.open(path, 'rb') as stream:
        archive = gate.strict(stream.read())
    for name, value in archive['files'].items():
        need(hashlib.sha256(value['text'].encode()).hexdigest() == value['sha256'], 'raw artifact digest differs: ' + name)
    return archive['files']


def archived_result(files, prefix, gate):
    command = gate.strict(files[prefix + '/command.json']['text'])
    stdout = files[prefix + '/stdout']['text'].encode()
    stderr = files[prefix + '/stderr']['text'].encode()
    need(command['timeout'] is False, 'recorded command timed out: ' + prefix)
    for stream, data in [('stdout', stdout), ('stderr', stderr)]:
        need(command[stream + '_sha256'] == hashlib.sha256(data).hexdigest() and
             command[stream + '_bytes'] == len(data), 'recorded output binding differs: ' + prefix)
    return subprocess.CompletedProcess(command['argv'], command['exit'], stdout, stderr)


def audit_archives(manifest, gate):
    inventory = gate.strict(ARTIFACTS.read_bytes())
    measured = read_archive('product-verification-macos-arm64.json.gz', inventory, gate)
    gates = read_archive('product-verification-gates.json.gz', inventory, gate)
    bindings = gate.strict((RESULTS / 'product-verification-sources.json').read_bytes())
    scope = gate.strict((HERE / 'scope.json').read_bytes())
    cases = {r['name']: r for r in manifest['cases']}
    records = gate.strict(measured['measurements-final/samples.json']['text'])
    need(len(records) == 351 and sum(not r['warmup'] for r in records) == 273, 'sample count differs')
    schedule = {r['case']: r for r in manifest['scalar_pair_schedule']}
    expected_keys = set()
    for row in manifest['cases']:
        if row['group'] not in ('scalar', 'product'):
            continue
        plan = schedule[row['name']] if row['group'] == 'scalar' else dict(warmups=['B'] * 2, samples=['B'] * 7)
        for phase in ('warmups', 'samples'):
            for pair, order in enumerate(plan[phase]):
                for letter in order:
                    expected_keys.add((row['name'], phase, pair, 'baseline' if letter == 'A' else 'candidate', order))
    observed_keys = []
    for record in records:
        phase = 'warmups' if record['warmup'] else 'samples'
        observed_keys.append((record['case'], phase, record['pair'], record['side'], record['order']))
        prefix = f"measurements-final/{record['case']}/{phase}/{record['pair']}/{record['side']}"
        stdout = measured[prefix + '/stdout']['text'].encode()
        stderr = measured[prefix + '/stderr']['text'].encode()
        command = gate.strict(measured[prefix + '/command.json']['text'])
        for key, value in command.items():
            need(gate.same(record[key], value), 'sample command binding differs: ' + prefix)
        need(hashlib.sha256(stdout).hexdigest() == command['stdout_sha256'] and
             hashlib.sha256(stderr).hexdigest() == command['stderr_sha256'], 'command output binding differs')
        need(record['passed'] is True and record['timeout'] is False, 'failed historical sample')
        result = subprocess.CompletedProcess(command['argv'], command['exit'], stdout, stderr)
        report = accept(gate, result, cases[record['case']], bindings['source_inputs'][record['side']]['release_binary_sha256'],
                        bindings['tools']['solver']['sha256'], scope)
        original = gates[f"preflight-final/{record['case']}/{record['side']}/verify/stdout"]['text']
        need(gate.same(gate.normalize(report), gate.normalize(gate.strict(original))), 'historical sample differs from preflight')
        need(gate.same(work(report, stdout), record['work']), 'historical work counters differ')
    need(len(observed_keys) == len(set(observed_keys)) and set(observed_keys) == expected_keys, 'sample schedule differs')
    need(gate.same(summarize(records), gate.strict(measured['measurements-final/summary.json']['text'])),
         'historical summary differs from raw samples')
    for row in manifest['cases']:
        reports = {}
        for side in ('baseline', 'candidate'):
            prefix = f"preflight-final/{row['name']}/{side}"
            if side == 'candidate' or row['group'] == 'scalar':
                result = archived_result(gates, prefix + '/verify', gate)
                reports[side] = accept(gate, result, row, bindings['source_inputs'][side]['release_binary_sha256'],
                                       bindings['tools']['solver']['sha256'], scope)
            runtime = row['runtime']
            result = archived_result(gates, prefix + '/runtime/eval', gate)
            need(result.returncode == runtime['exit'], 'recorded runtime exit differs')
            if 'stdout' in runtime:
                need(gates[prefix + '/runtime/eval/stdout']['text'] == runtime['stdout'] and
                     not gates[prefix + '/runtime/eval/stderr']['text'], 'recorded runtime value differs')
            else:
                need(runtime['diagnostic'] in gates[prefix + '/runtime/eval/stderr']['text'], 'recorded runtime trap differs')
            result = archived_result(gates, prefix + '/runtime/dump-core', gate)
            need(result.returncode == 0 and not result.stderr, 'recorded core generation rejected')
            gate.strict(result.stdout)
            result = archived_result(gates, prefix + '/runtime/eval-core', gate)
            need(result.returncode == runtime['exit'], 'recorded typed runtime exit differs')
            core = gate.strict(result.stdout)
            need(gate.same(core, runtime['typed']), 'recorded typed runtime result differs')
        if len(reports) == 2:
            need(gate.same(gate.normalize(reports['baseline']), gate.normalize(reports['candidate'])), 'recorded scalar pair differs')
        a = gates[f"preflight-final/{row['name']}/baseline/runtime/dump-core/stdout"]['text']
        b = gates[f"preflight-final/{row['name']}/candidate/runtime/dump-core/stdout"]['text']
        need(a == b, 'recorded erasure/core pair differs')
    return dict(result='PASS', raw_samples=351, measured_samples=273, preflight_cases=33,
                runtime_core_pairs=33, project_commands_executed=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['audit', 'gate', 'time'])
    for name in ('baseline', 'candidate', 'solver', 'baseline-source', 'candidate-source', 'out'):
        parser.add_argument('--' + name, type=Path)
    parser.add_argument('--new-host', action='store_true', help='record explicit new executable hashes without relabeling historical data')
    for name in ('baseline', 'candidate', 'solver'):
        parser.add_argument('--' + name + '-sha256')
    parser.add_argument('--rustc', type=Path, help='real pinned toolchain executable; rustup proxies are rejected')
    parser.add_argument('--cargo', type=Path, help='real pinned toolchain executable; rustup proxies are rejected')
    args = parser.parse_args()
    if args.mode == 'audit':
        manifest, gate = audit()
        print(json.dumps(audit_archives(manifest, gate)))
        return
    for name in ('baseline', 'candidate', 'solver', 'baseline_source', 'candidate_source', 'rustc', 'cargo', 'out'):
        need(getattr(args, name) is not None, '--' + name.replace('_', '-') + ' is required')
        setattr(args, name, getattr(args, name).resolve())
    if args.new_host:
        for name in ('baseline_sha256', 'candidate_sha256', 'solver_sha256'):
            need(getattr(args, name), '--' + name.replace('_', '-') + ' is required with --new-host')
    if args.mode == 'gate':
        preflight(args)
    else:
        measure(args)


if __name__ == '__main__':
    main()
