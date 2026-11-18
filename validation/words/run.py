#!/usr/bin/env python3
"""Finite word-revision conformance through real compiler, formal, and native boundaries."""
from pathlib import Path
import argparse, ast, hashlib, json, os, platform, shlex, sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SHARED = HERE.parent / 'memory'
sys.path.insert(0, str(SHARED))
from capture import Runner, save
import oracle as LEGACY
sys.path.pop(0)
import words_oracle as O
from reference_protocol import protocol
GROUPS = ('source', 'raw', 'traces', 'controls', 'bounds', 'resources')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for data in iter(lambda: f.read(1048576), b''):
            h.update(data)
    return h.hexdigest()


def identity(path):
    p = Path(path).resolve(strict=True)
    return dict(path=str(p), bytes=p.stat().st_size, sha256=digest(p))


def read(path, limit=8388608):
    with Path(path).open('rb') as f:
        data = f.read(limit + 1)
    O.need(len(data) <= limit, 'retained file exceeds bound: ' + str(path))
    return data


def audit():
    seal = O.strict((HERE / 'INTEGRITY.json').read_bytes())
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name != 'INTEGRITY.json'}
    O.need(actual == set(seal['files']), 'word package inventory changed')
    for name, expected in seal['files'].items():
        p = HERE / name
        O.need(not p.is_symlink() and p.is_file(), 'missing/symlinked package file')
        O.need(p.stat().st_size == expected['bytes'] and digest(p) == expected['sha256'], 'package bytes changed: ' + name)
    for name, expected in seal['shared'].items():
        p = SHARED / name
        O.need(p.stat().st_size == expected['bytes'] and digest(p) == expected['sha256'], 'shared memory helper changed: ' + name)
    m = O.strict((HERE / 'manifest.json').read_bytes())
    O.need((len(m['source']), len(m['raw']), len(m['pairs']), len(m['traces'])) == (68, 36, 3, 6), 'sealed primary corpus counts')
    for row in m['source']:
        O.need(digest(HERE / row['source']) == row['sha256'], 'source fixture changed')
    for row in m['raw']:
        O.need(digest(HERE / row['path']) == row['sha256'], 'raw fixture changed')
    for row in m['traces']:
        for kind in ('trace', 'plan'):
            r = row['files'][kind]
            O.need(digest(HERE / r['path']) == r['sha256'], 'trace/plan fixture changed')
        O.validate_trace(O.strict(read(HERE / row['files']['trace']['path'])), m['allocation_profile'], replay=True)
    for p in HERE.glob('*.py'):
        ast.parse(p.read_text(), filename=str(p))
    return m


class Gate:
    def __init__(self, args, manifest):
        self.m = manifest
        self.root = args.out.resolve()
        self.groups = args.groups.split(',')
        O.need(len(self.groups) == len(set(self.groups)) and set(self.groups) <= set(GROUPS), 'unknown/repeated group')
        O.need(not self.root.exists() and HERE not in self.root.parents and self.root != HERE, 'fresh output directory required')
        self.tool_record = args.tools.resolve(strict=True)
        records = O.strict(read(self.tool_record))
        O.keys(records, ('schema', 'tools'))
        O.need(records['schema'] == 'anl-words-validation-tools-v1', 'tool record schema')
        requirements = {
            'source': ('rust', 'evidence', 'exporter', 'rust_mir', 'pair', 'raw', 'reference', 'cc'),
            'raw': ('rust', 'evidence', 'exporter', 'rust_mir', 'raw', 'pair', 'reference'),
            'traces': ('rust', 'evidence', 'exporter', 'rust_mir', 'raw', 'pair', 'reference', 'cc'),
            'controls': ('rust', 'evidence', 'exporter', 'rust_mir', 'raw', 'pair', 'reference', 'cc', 'old_scalar', 'old_products', 'old_raw'),
            'bounds': ('rust', 'evidence', 'rust_mir', 'raw', 'pair', 'reference'),
            'resources': ('rust', 'evidence', 'exporter', 'rust_mir', 'raw', 'pair', 'reference'),
        }
        required = set().union(*(requirements[g] for g in self.groups))
        configurations = dict(rust='default', evidence='memory-evidence', exporter='memory-evidence', rust_mir='memory-evidence')
        self.tools, self.identities, self.provenance = {}, {}, {}
        for name in sorted(required):
            row = records['tools'][name]
            p = Path(row['path']).resolve(strict=True)
            O.need(p.is_file() and os.access(p, os.X_OK), 'tool is not executable: ' + name)
            actual = identity(p)
            O.need(actual['sha256'] == row['sha256'] and actual['bytes'] == row['bytes'], 'tool identity differs: ' + name)
            self.tools[name], self.identities[name] = p, actual
            if name != 'cc':
                O.need(row['configuration'] == configurations.get(name, 'formal'), 'tool configuration differs: ' + name)
                source = row['source_manifest']
                bound = identity(source['path'])
                O.need(bound['sha256'] == source['sha256'], 'source/build manifest differs: ' + name)
                self.provenance[name] = bound
        for family in [('rust', 'evidence', 'exporter', 'rust_mir'), ('pair', 'raw', 'reference')]:
            O.need(len({self.provenance[n]['sha256'] for n in family if n in self.provenance}) <= 1, 'mixed source/build manifest in tool family')
        self.root.mkdir(parents=True, exist_ok=False)
        self.runner, self.rows, self.bundles = Runner(self.root, manifest), [], {}
        self.before_tools, self.package = identity(self.tool_record), identity(HERE / 'INTEGRITY.json')
        self.wrappers = {}
        for name, script in [('cc', HERE / 'cc_adapter.py'), ('spy', SHARED / 'tool_spy.py')]:
            path = self.root / (name + '-launcher')
            path.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' + shlex.quote(str(script)) + ' "$@"\n')
            path.chmod(0o700)
            self.wrappers[name] = path
        save(self.root / 'IDENTITY.json', dict(tools=self.identities, source_manifests=self.provenance,
            tool_record=self.before_tools, package=self.package, groups=self.groups, python=identity(sys.executable),
            host=dict(system=platform.system(), release=platform.release(), machine=platform.machine()),
            performance_metrics_collected=False, provenance_claim='Hashes bind explicitly supplied build records; build/proof qualification is separate.'))

    def call(self, label, argv, inputs=(), env=None, native=False):
        before = [identity(p) for p in inputs]
        executable = identity(argv[0])
        name = f"{self.runner.count + 1:04d}-{label}"
        pending = self.root / 'command-bindings' / (name + '.json')
        folder = self.root / 'commands' / name
        binding = dict(executable=executable, inputs=before, state='before_launch')
        save(pending, binding)
        try:
            r = self.runner.run(label, argv, env, timeout=self.m['native_timeout_seconds'] if native else None)
        finally:
            checks = []
            for expected in [executable, *before]:
                try:
                    actual = identity(expected['path'])
                    checks.append(dict(expected=expected, actual=actual, unchanged=actual == expected))
                except (OSError, ValueError) as error:
                    checks.append(dict(expected=expected, unchanged=False, error=str(error)))
            binding.update(state='after_attempt', checks=checks,
                           identities_unchanged=all(c['unchanged'] for c in checks))
            save(pending, binding)
            if folder.is_dir(): save(folder / 'bindings.json', binding)
        O.need(binding['identities_unchanged'], 'command changed its tool/input')
        return r

    def cli(self, tool, command, path, *args):
        return [self.tools[tool], command, path, *args]

    def success(self, r):
        O.need(r['exit'] == 0 and r['stdout'] == b'' and r['stderr'] == b'', 'nonexecuting command failed/published output')

    def row(self, name, **claims):
        self.rows.append(dict(case=name, status='PASS', **claims))
        save(self.root / 'ROWS.json', self.rows)

    def expected(self, completion):
        if completion['kind'] == 'value':
            return dict(outcome='value', type='i64', value=completion['value'])
        if completion['kind'] == 'trap':
            return dict(outcome='trap', trap=completion['trap'])
        return dict(outcome='resource_limit')

    def execute(self, label, tool, command, path, expected, fuel=100000, env=None, inputs=()):
        r = self.call(label, self.cli(tool, command, path, '--fuel', fuel), [path, *inputs], env)
        O.assert_execution(r, self.expected(expected), wire=command == 'eval-core')
        return r

    def raw(self, kind, path, accepted, label):
        r = self.call(label + '-formal', [self.tools['raw'], kind, path], [path])
        doc = O.strict(r['stdout']); O.keys(doc, ('raw_valid', 'reason'))
        O.need(r['exit'] == (0 if accepted else 1) and not r['stderr'] and doc['raw_valid'] is accepted, 'formal raw judgment')
        O.need(type(doc['reason']) is str and (doc['reason'] == '') == accepted, 'raw diagnostic classification')
        if kind == 'mir':
            r = self.call(label + '-rust', [self.tools['rust_mir'], path], [path])
            O.need(r['exit'] == (0 if accepted else 1) and r['stdout'] == (b'accepted\n' if accepted else b'invalid_ir\n'), 'Rust MIR judgment')

    def pair(self, label, core, mir, accepted=True):
        r = self.call(label, [self.tools['pair'], core, mir], [core, mir])
        O.assert_pair_report(r, 'accepted' if accepted else 'rejected', self.m['allocation_profile'])
        O.need(not r['stderr'], 'pair stderr')

    def bundle(self, label, path, memory, imported=False):
        key = (str(path), imported)
        if key in self.bundles:
            return self.bundles[key]
        bundle = self.root / 'bundles' / label; bundle.parent.mkdir(exist_ok=True)
        args = [self.tools['exporter'], *(['--core'] if imported else []), path, bundle]
        self.success(self.call(label + '-export', args, [path]))
        m = O.strict(read(bundle / 'manifest.json'))
        O.keys(m, ('schema', 'semantic_revision', 'allocation_profile', 'has_memory', 'runtime', 'compiler', 'files', 'sources'))
        files = {'core.json', 'mir.json', 'program.c'} | ({'runtime.c', 'runtime.h'} if memory else set())
        O.need(m['schema'] == 'anl-words-evidence-bundle-v1' and m['semantic_revision'] == O.REVISION, 'bundle revision')
        O.need(m['has_memory'] is memory and m['runtime'] == ('default' if memory else 'none'), 'profile/memory/runtime conflated')
        O.need(O.same(m['allocation_profile'], self.m['allocation_profile']), 'bundle profile')
        O.need(set(m['files']) == files and {p.name for p in bundle.iterdir()} == files | {'manifest.json'}, 'bundle file inventory')
        O.need(m['compiler']['sha256'] == self.identities['exporter']['sha256'] and m['compiler']['memory_evidence'] is True, 'exporter binary identity')
        for name, expected in m['files'].items():
            actual = identity(bundle / name)
            O.need(actual['sha256'] == expected['sha256'] and actual['bytes'] == expected['bytes'], 'bundle file binding')
        if imported:
            O.need(m['sources'] == [], 'raw import fabricated source provenance')
        else:
            O.need(m['sources'] == [dict(path_bytes_hex=os.fsencode(path).hex(), bytes=path.stat().st_size, sha256=digest(path))], 'bundle source identity')
            dumped = self.call(label + '-dump', self.cli('rust', 'dump-core', path), [path])
            O.need(dumped['exit'] == 0 and not dumped['stderr'] and dumped['stdout'] == read(bundle / 'core.json'), 'actual source Core bytes differ')
        core = O.strict(read(bundle / 'core.json'))
        O.need(core['schema'] == 'anl-core-v4' and core['semantic_revision'] == O.REVISION, 'explicit Core v4 provenance lost')
        self.raw('core', bundle / 'core.json', True, label + '-core')
        self.raw('mir', bundle / 'mir.json', True, label + '-mir')
        self.pair(label + '-actual-pair', bundle / 'core.json', bundle / 'mir.json')
        self.bundles[key] = bundle
        return bundle

    def reference(self, label, core, expected, plan=None, trace=None, fuel=100000, transitions=262144, reason=None):
        plan = plan or HERE / self.m['empty_plan']
        r = self.call(label, [self.tools['reference'], core, plan, fuel, transitions], [core, plan])
        row = dict(fuel=fuel, transitions=transitions, profile=self.m['allocation_profile'], status=expected['kind'])
        report = protocol(r, row, O.heap_sites(O.strict(read(core))))
        if report['status'] in ('transition_limit', 'error'):
            raise O.Inconclusive('reference did not complete: ' + report['reason'])
        O.need(report['status'] == expected['kind'] and report['resource_reason'] == reason, 'reference outcome/resource reason differs')
        O.need(O.same(O.outcome(report['trace']['completion']), self.expected(expected)), 'reference completion differs')
        if trace:
            O.need(O.same(report['trace'], O.strict(read(trace))), 'reference full trace differs')
        else:
            O.need(report['trace']['events'] == [], 'pure reference fabricated memory events')
        return report

    def trace_options(self, label, replay):
        path = self.root / 'traces' / (label + '.json'); path.parent.mkdir(exist_ok=True)
        O.need(not path.exists(), 'trace destination not fresh')
        return path, dict(ANL_MEMORY_TRACE=path, ANL_MEMORY_REPLAY=replay)

    def native(self, label, tool, source, bundle, expected, memory, replay=None, expected_trace=None, inactive=False):
        O.need(expected['kind'] in ('value', 'trap'), 'resource/noncompleted case must never run native')
        binary = self.root / 'native' / label; binary.parent.mkdir(exist_ok=True)
        cc_log = self.root / 'cc' / label
        env = dict(CC=self.wrappers['cc'], ANL_CORPUS_SCRATCH=self.root, ANL_CORPUS_REAL_CC=self.tools['cc'],
                   ANL_CORPUS_REAL_CC_SHA256=self.identities['cc']['sha256'], ANL_CORPUS_CC_LOG=cc_log)
        trace = None
        if replay is not None or inactive:
            trace, controls = self.trace_options(label, replay if replay is not None else self.root / 'absent-replay')
            env.update(controls)
        self.success(self.call(label + '-build', self.cli(tool, 'build', source, '-o', binary), [source, *([replay] if replay else [])], env, native=True))
        artifact = identity(binary)
        r = self.call(label + '-execute', [binary], [binary], native=True)
        O.assert_execution(r, self.expected(expected))
        O.need(identity(binary) == artifact, 'published native binary changed during execution')
        m = O.strict(read(bundle / 'manifest.json')); records = []
        for p in sorted(cc_log.glob('call-*/command.json')):
            c = O.strict(read(p)); O.need(c['real_cc_sha256'] == self.identities['cc']['sha256'] and c['changed_arguments'] is False and c['exit'] == 0, 'C adapter/identity failure')
            for item in c['inputs']:
                data = read(p.parent / item['file'], 67108864)
                O.need(len(data) == item['bytes'] and O.sha(data) == item['sha256'], 'captured C input changed')
            output = c['output']; data = read(p.parent / 'output.bin', 67108864)
            O.need(len(data) == output['bytes'] and O.sha(data) == output['sha256'], 'captured object/artifact changed')
            records.append(c)
        O.need(records and artifact['sha256'] in {x['output']['sha256'] for x in records}, 'native artifact is not the captured compiler output')
        sources = {}
        for c in records:
            for item in c['inputs']:
                if Path(item['path']).suffix in ('.c', '.h'):
                    sources.setdefault(Path(item['path']).name, set()).add(item['sha256'])
        for name in ('program.c', 'runtime.c', 'runtime.h'):
            if name in m['files']:
                O.need(sources.get(name) == {m['files'][name]['sha256']}, 'actual C bytes differ from exporter: ' + name)
        activated = replay is not None and memory
        O.need(set(sources) == ({'program.c', 'runtime.c', 'runtime.h'} if memory else {'program.c'}) | ({'evidence.h'} if activated else set()), 'unexpected native source/config input')
        if memory:
            compiles = [c for c in records if any(i['path'].endswith('.c') for i in c['inputs'])]
            links = [c for c in records if '-c' not in c['argv']]
            O.need(len(compiles) == 2 and len(links) == 1, 'program/runtime must compile separately then link')
            for c in compiles:
                O.need('-c' in c['argv'] and '-fno-lto' in c['argv'], 'opaque runtime compilation flags')
                O.need(('-DANL_MEMORY_EVIDENCE=1' in c['argv']) == activated, 'evidence compilation mode')
            linked = {i['sha256'] for i in links[0]['inputs'] if i['path'].endswith('.o')}
            O.need(linked == {c['output']['sha256'] for c in compiles}, 'link inputs differ from captured program/runtime objects')
        if expected_trace:
            O.assert_trace(read(trace), O.strict(read(expected_trace)))
        elif trace:
            O.need(not trace.exists(), 'inactive/pure program emitted native memory trace')
        save(cc_log / 'ARTIFACT-BINDING.json', dict(artifact=artifact, bundle=str(bundle), actual_inputs_retained=True,
            runtime='activated' if activated else 'default' if memory else 'none', native_trace_applicable=activated))

    def source_group(self):
        for row in self.m['source']:
            name, path, expected = row['id'], HERE / row['source'], row['expected']
            rejected = expected['kind'] == 'source_rejection'
            marker = self.root / 'spies' / (name + '.jsonl'); marker.parent.mkdir(exist_ok=True)
            env = dict(CC=self.wrappers['spy'], ANL_CORPUS_SPY_LOG=marker)
            for tool in ('rust', 'evidence'):
                r = self.call(name + '-' + tool + '-check', self.cli(tool, 'check', path), [path], env)
                O.need(r['exit'] == (1 if rejected else 0) and not r['stdout'] and bool(r['stderr']) == rejected, 'source check classification')
                if rejected:
                    r = self.call(name + '-' + tool + '-reject', self.cli(tool, 'eval', path), [path], env)
                    O.need(r['exit'] == 1 and not r['stdout'] and r['stderr'], 'invalid source began evaluation')
                else:
                    self.execute(name + '-' + tool + '-eval', tool, 'eval', path, expected, env=env)
            O.need(not marker.exists(), 'source checking/evaluation started compiler')
            if rejected:
                self.row(name, source_rejection=True, native_exclusion='source rejected before execution'); continue
            bundle = self.bundle(name, path, row['memory'])
            trace_row = next((r for r in self.m['traces'] if r['source'] == row['source']), None)
            trace = HERE / trace_row['files']['trace']['path'] if trace_row else None
            plan = HERE / trace_row['files']['plan']['path'] if trace_row else None
            self.reference(name + '-reference', bundle / 'core.json', expected, plan, trace)
            for tool in ('rust', 'evidence'):
                self.execute(name + '-' + tool + '-core', tool, 'eval-core', bundle / 'core.json', expected)
            self.native(name + '-default', 'rust', path, bundle, expected, row['memory'])
            self.row(name, actual_export_pair=True, formal_reference=True, native_routes=['default-build'], native_trace_applicable=False)

    def raw_group(self):
        expected_values = {'pure-word': '42', 'legacy-only-v4': '42', 'identity-conversion': '42', 'u64-full-range': '1'}
        for row in self.m['raw']:
            label = 'raw-' + row['kind'] + '-' + row['id']; path = HERE / row['path']
            self.raw(row['kind'], path, row['accepted'], label)
            if row['kind'] == 'core':
                for tool in ('rust', 'evidence'):
                    r = self.call(label + '-' + tool, self.cli(tool, 'eval-core', path, '--fuel', 0), [path])
                    O.assert_execution(r, dict(outcome='resource_limit' if row['accepted'] else 'invalid_ir'), wire=True)
                if row['accepted']:
                    expected = dict(kind='value', value=expected_values[row['id']])
                    self.reference(label + '-original-reference', path, expected)
                    bundle = self.bundle(label, path, False, imported=True)
                    O.need(O.same(O.strict(read(path)), O.strict(read(bundle / 'core.json'))), 'canonical export changed raw checked program')
                    self.reference(label + '-canonical-reference', bundle / 'core.json', expected)
                    for tool in ('rust', 'evidence'):
                        self.execute(label + '-' + tool + '-original', tool, 'eval-core', path, expected)
                        self.execute(label + '-' + tool + '-canonical', tool, 'eval-core', bundle / 'core.json', expected)
                    bindings = self.root / 'raw-bindings'; bindings.mkdir(exist_ok=True)
                    save(bindings / (label + '.json'), dict(original=identity(path), canonical=identity(bundle / 'core.json'), original_bytes_retained=True))
            self.row(label, raw_acceptance=row['accepted'], native_exclusion='raw fixture; no native route selected')
        for i, row in enumerate(self.m['pairs']):
            self.pair('raw-pair-' + str(i), HERE / row['core'], HERE / row['mir'], row['accepted'])
            self.row('raw-pair-' + str(i), canonical_acceptance=row['accepted'])

    def trace_case(self, label, source, plan, trace):
        expected = O.strict(read(trace))['completion']
        bundle = self.bundle(label, source, True)
        self.reference(label + '-reference', bundle / 'core.json', expected, plan, trace)
        for command, path in [('eval', source), ('eval-core', bundle / 'core.json')]:
            dest, env = self.trace_options(label + '-' + command, trace)
            self.execute(label + '-' + command, 'evidence', command, path, expected, env=env, inputs=[trace])
            O.assert_trace(read(dest), O.strict(read(trace)))
        self.native(label + '-native', 'evidence', source, bundle, expected, True, trace, trace)
        self.row(label, exact_reference_evaluator_native_trace=True, native_routes=['evidence-build'])

    def traces_group(self):
        for row in self.m['traces']:
            self.trace_case('trace-' + row['id'], HERE / row['source'], HERE / row['files']['plan']['path'], HERE / row['files']['trace']['path'])
        for row in self.m['effects']:
            self.trace_case(row['id'], HERE / row['source'], HERE / row['plan'], HERE / row['trace'])

    def controls_group(self):
        marker = self.root / 'spies' / 'controls.jsonl'; marker.parent.mkdir(exist_ok=True)
        spy = dict(CC=self.wrappers['spy'], ANL_CORPUS_SPY_LOG=marker,
                   ANL_MEMORY_TRACE='', ANL_MEMORY_REPLAY=self.root / 'absent-replay')
        for row in self.m['verify']:
            path = HERE / row['source']; files = [HERE / f for f in row['files']]
            for tool in ('rust', 'evidence'):
                r = self.call('verify-' + row['id'] + '-' + tool,
                    self.cli(tool, 'verify', path, '--json', '--solver', self.wrappers['spy']), files, spy)
                O.need(r['exit'] == 7, 'word verification must be unsupported')
                doc = O.strict(r['stdout'])
                for key, expected in dict(schema='anl-verify-v5', semantic_revision=O.REVISION,
                    verification_revision='anl-words-unsupported-v1', status='unsupported', trust='not_established',
                    type_checked=True, tested=False, dynamic_checks=False, contracts_erased=True,
                    compiler=None, solver=None, obligations=[]).items():
                    O.need(key in doc and O.same(doc[key], expected), 'unsupported report field: ' + key)
                O.need('scope' in doc and O.same(doc['scope'], dict(functions='all_loaded',
                    arithmetic_safety=False, partial_correctness=False, termination_proved=False,
                    native_correctness=False, model_proof=None, fragment='words_unsupported')),
                    'unsupported verification claimed a proof or omitted its exact scope')
                O.need(len(doc['functions']) == row['functions'] and len(doc['sources']) == row['sources'], 'whole loaded graph omitted')
                O.need([f['id'] for f in doc['functions']] == list(range(row['functions'])), 'function metadata IDs')
                reported = {(x['path_bytes_hex'], x['sha256'], x['bytes']) for x in doc['sources']}
                O.need(reported == {(os.fsencode(p).hex(), digest(p), p.stat().st_size) for p in files}, 'loaded source hashes omitted')
            self.row('verify-' + row['id'], unsupported_before_tools=True)
        bad = HERE / self.m['source_error']
        for tool in ('rust', 'evidence'):
            for command in ('verify', 'build'):
                output = self.root / ('source-error-' + tool)
                extra = ['--json', '--solver', self.wrappers['spy']] if command == 'verify' else ['-o', output]
                r = self.call('error-before-' + tool + '-' + command, self.cli(tool, command, bad, *extra), [bad], spy)
                O.need(r['exit'] == 1 and not output.exists(), 'source error did not precede unsupported/build routing')
                if command == 'verify':
                    O.need(O.strict(r['stdout'])['type_checked'] is False, 'invalid source partially verified')
        O.need(not marker.exists(), 'unsupported/error path started a compiler or solver')
        for row in self.m['legacy']:
            path = HERE / row['path']; name = row['id']; accepted = row['accepted']
            if row['kind'] == 'core':
                r = self.call(name + '-rust', self.cli('rust', 'eval-core', path, '--fuel', 0), [path])
                O.assert_execution(r, dict(outcome='resource_limit' if accepted else 'invalid_ir'), wire=True)
                tool = row['formal']
                args = [self.tools[tool], 'core', path] if tool == 'old_raw' else [self.tools[tool], path, '--fuel', 0]
                r = self.call(name + '-old-formal', args, [path])
                if tool == 'old_raw':
                    doc = O.strict(r['stdout']); O.keys(doc, ('raw_valid', 'reason'))
                    O.need(r['exit'] == (0 if accepted else 1) and doc['raw_valid'] is accepted, 'old Core reader capability changed')
                else:
                    O.assert_execution(r, dict(outcome='resource_limit' if accepted else 'invalid_ir'), wire=True)
            else:
                for tool in ('rust_mir', 'old_raw'):
                    args = [self.tools[tool], path] if tool == 'rust_mir' else [self.tools[tool], 'mir', path]
                    r = self.call(name + '-' + tool, args, [path])
                    O.need(r['exit'] == (0 if accepted else 1), 'old MIR reader capability changed')
                    if tool == 'old_raw':
                        doc = O.strict(r['stdout']); O.keys(doc, ('raw_valid', 'reason'))
                        O.need(doc['raw_valid'] is accepted, 'old MIR raw report')
                    else:
                        O.need(r['stdout'] == (b'accepted\n' if accepted else b'invalid_ir\n'), 'old MIR transport report')
            self.row(name, historical_reader_acceptance=accepted)
        names = HERE / self.m['legacy_names']
        for tool in ('rust', 'evidence'):
            self.execute('legacy-names-' + tool, tool, 'eval', names, dict(kind='value', value='42'))
            r = self.call('legacy-names-dump-' + tool, self.cli(tool, 'dump-core', names), [names])
            O.need(r['exit'] == 0 and O.strict(r['stdout'])['schema'] == 'apl-core-v0', 'contextual names forced word revision')
        old = HERE / self.m['old_memory']; replay = HERE / self.m['old_unknown_trap']
        for command in ('eval', 'build'):
            dest, env = self.trace_options('old-reject-shift-' + command, replay)
            env.update(CC=self.wrappers['spy'], ANL_CORPUS_SPY_LOG=marker)
            binary = self.root / 'must-not-publish'
            r = self.call('old-reject-shift-' + command, self.cli('evidence', command, old, *(['-o', binary] if command == 'build' else [])), [old, replay], env)
            O.need(r['exit'] == 4 and not r['stdout'] and r['stderr'] and not dest.exists() and not binary.exists(), 'old trace admitted new trap')
        O.need(not marker.exists(), 'replay preflight started compiler')
        pure = HERE / 'source/wrap-add-u8.anl'; expected = dict(kind='value', value='0')
        bundle = self.bundle('pure-controls', pure, False)
        for tool in ('rust', 'evidence'):
            for command, path in [('eval', pure), ('eval-core', bundle / 'core.json')]:
                dest, env = self.trace_options('pure-' + tool + '-' + command, self.root / 'missing-replay')
                self.execute('pure-' + tool + '-' + command, tool, command, path, expected, env=env)
                O.need(not dest.exists(), 'profile-only program activated memory evidence')
            self.native('pure-' + tool, tool, pure, bundle, expected, False, inactive=True)
        # The default binary ignores controls even when the authored program uses memory.
        row = self.m['traces'][0]; source = HERE / row['source']; expected = O.strict(read(HERE / row['files']['trace']['path']))['completion']
        bundle = self.bundle('default-memory-controls', source, True)
        dest, env = self.trace_options('default-memory-eval', self.root / 'missing-replay')
        self.execute('default-memory-eval', 'rust', 'eval', source, expected, env=env)
        O.need(not dest.exists(), 'default compiler consulted evidence controls')
        self.native('default-memory-build', 'rust', source, bundle, expected, True, inactive=True)
        # These exercise the actual corrected CLI write/flush path, with real stdout failure.
        readonly = self.root / 'readonly-output'; readonly.write_bytes(b'unchanged')
        for tool, args in [('rust_mir', [HERE / 'mir/pure-word.json']),
                           ('raw', ['core', HERE / 'core/pure-word.json']),
                           ('pair', [HERE / 'core/pure-word.json', HERE / 'mir/pure-word.json']),
                           ('reference', [HERE / 'core/pure-word.json', HERE / self.m['empty_plan'], 100, 1000])]:
            r = self.call('closed-stdout-' + tool, [sys.executable, HERE / 'closed_stdout.py', readonly, self.tools[tool], *args],
                [readonly, self.tools[tool], *[p for p in args if isinstance(p, Path)]])
            O.need(r['exit'] == 4 and r['stdout'] == b'' and r['stderr'] and readonly.read_bytes() == b'unchanged', 'failed report write returned success/changed file')
        self.row('controls', pure_trace_absent=True, default_controls_ignored=True, old_unknown_trap_rejected=True, actual_closed_stdout=True)

    def resources_group(self):
        for row in self.m['resources']:
            O.need(row['native'] is False, 'resource fixture native prohibition changed')
            core, plan, trace, replay = [HERE / row[k] for k in ('core', 'plan', 'trace', 'replay')]
            expected = dict(kind='resource_limit')
            self.reference('resource-' + row['id'], core, expected, plan, trace, row['fuel'], row['transitions'], row['reason'])
            for tool in (('rust', 'evidence') if row['default'] else ('evidence',)):
                dest, env = self.trace_options('resource-' + row['id'] + '-' + tool, replay)
                r = self.execute('resource-' + row['id'] + '-' + tool, tool, 'eval-core', core, expected, row['fuel'], env, [replay])
                suffix = ': resource_limit: ' + self.m['resource_diagnostics'][row['reason']] + '\n'
                O.need(r['stderr'].endswith(suffix.encode()), 'evaluator resource reason differs')
                if tool == 'evidence': O.assert_trace(read(dest), O.strict(read(trace)))
                else: O.need(not dest.exists(), 'default resource route activated evidence')
            self.row('resource-' + row['id'], resource_reason=row['reason'], native_exclusion='resource-only fixture, never compiled or run natively')
        path = HERE / self.m['depth_resource']; expected = dict(kind='resource_limit')
        bundle = self.bundle('recursive-depth', path, False)
        self.reference('recursive-depth-reference', bundle / 'core.json', expected, fuel=100000, reason='depth')
        for tool in ('rust', 'evidence'):
            r = self.execute('recursive-depth-' + tool, tool, 'eval', path, expected)
            O.need(self.m['resource_diagnostics']['depth'].encode() in r['stderr'], 'runtime expression-depth reason')
        self.row('recursive-depth', resource_reason='depth', native_exclusion='nonterminating recursion bounded only by interpreter resource policy')

    def bounds_group(self):
        from bounds import generate
        folder = self.root / 'boundaries'; folder.mkdir()
        for row in self.m['boundaries']:
            data = generate(row, HERE)
            O.need(len(data) == row['bytes'] and O.sha(data) == row['sha256'], 'generated boundary input changed')
            path = folder / (row['id'] + '.json'); path.write_bytes(data)
            kind = row['kind']
            if kind in ('core', 'mir'):
                r = self.call(row['id'] + '-formal', [self.tools['raw'], kind, path], [path])
                doc = O.strict(r['stdout']); O.keys(doc, ('raw_valid', 'reason'))
                O.need(r['exit'] == row['formal_exit'] and not r['stderr'] and doc['raw_valid'] is (row['formal_exit'] == 0), 'formal boundary classification')
                if kind == 'core':
                    r = self.call(row['id'] + '-rust', self.cli('rust', 'eval-core', path, '--fuel', 1000), [path])
                    expected = dict(outcome='value', type='i64', value='42') if row['rust_exit'] == 0 else dict(outcome='resource_limit')
                    O.assert_execution(r, expected, wire=True)
                else:
                    r = self.call(row['id'] + '-rust', [self.tools['rust_mir'], path], [path])
                    O.need(r['exit'] == row['rust_exit'] and r['stdout'] == (b'accepted\n' if row['rust_exit'] == 0 else b'resource_limit\n'), 'Rust MIR boundary classification')
            elif kind == 'mir-transport':
                r = self.call(row['id'], [self.tools['rust_mir'], path], [path])
                O.need(r['exit'] == row['rust_exit'] and r['stdout'] == (row['report'] + '\n').encode()
                    and r['stderr'], 'MIR transport byte/UTF-8 classification')
            elif kind == 'plan':
                core = HERE / 'core/pure-word.json'
                r = self.call(row['id'], [self.tools['reference'], core, path, 0, 0], [core, path])
                doc = protocol(r, dict(fuel=0, transitions=0, profile=self.m['allocation_profile'], status='boundary'), set())
                O.need(r['exit'] == row['reference_exit'] and doc['status'] == row['reference_status'], 'response-plan boundary/preflight classification')
                if doc['status'] == 'transition_limit': O.need(doc['trace']['events'] == [], 'zero-transition plan allocated')
            else:
                source = HERE / 'source/view-with-word-arguments.anl'
                dest, env = self.trace_options(row['id'], path)
                r = self.call(row['id'], self.cli('evidence', 'eval', source, '--fuel', 0), [source, path], env)
                O.need(r['exit'] == row['evidence_exit'] and not r['stdout'], 'replay boundary classification')
                if row['evidence_exit'] == 4:
                    O.need(not dest.exists(), 'invalid replay began execution')
                else:
                    expected = dict(schema='anl-words-trace-v1', semantic_revision=O.REVISION,
                        allocation_profile=self.m['allocation_profile'], events=[], completion=dict(kind='resource_limit'))
                    O.assert_trace(read(dest), expected)
            self.row(row['id'], boundary_kind=kind, native_exclusion='reader/resource boundary, never run natively')
        for name, minimum in [('legacy-only-v4', 1), ('identity-conversion', 2), ('pure-word', 2)]:
            core = HERE / 'core' / (name + '.json')
            for fuel in (minimum - 1, minimum):
                expected = dict(kind='value', value='42') if fuel == minimum else dict(kind='resource_limit')
                for tool in ('rust', 'evidence'):
                    self.execute('meter-' + name + '-' + tool + '-' + str(fuel), tool, 'eval-core', core, expected, fuel)
                self.reference('meter-' + name + '-formal-' + str(fuel), core, expected, fuel=fuel,
                    reason=None if fuel == minimum else 'expression_fuel')
            self.row('meter-' + name, minimum_expression_fuel=minimum, native_exclusion='fuel is tool policy')
        for name, core, plan, status in [('valid', HERE / 'core/pure-word.json', HERE / self.m['empty_plan'], 5),
            ('invalid-core', HERE / 'core/word-oversized.json', HERE / self.m['empty_plan'], 1)]:
            r = self.call('zero-transition-' + name, [self.tools['reference'], core, plan, 0, 0], [core, plan])
            doc = protocol(r, dict(fuel=0, transitions=0, profile=self.m['allocation_profile'], status='rejected' if status == 1 else 'boundary'), set())
            O.need(r['exit'] == status, 'checking must precede zero-step stop')
            if status == 5: O.need(doc['trace']['events'] == [] and doc['meter']['fuel_remaining'] == '0', 'zero budget changed initial resources')
        self.row('zero-transition', checking_precedes_execution=True)

    def check_identities(self):
        checks = []
        expected = [('tool_record', self.before_tools), ('package', self.package)]
        expected += [('tool:' + n, value) for n, value in self.identities.items()]
        expected += [('source_manifest:' + n, value) for n, value in self.provenance.items()]
        for name, before in expected:
            try:
                actual = identity(before['path'])
                checks.append(dict(name=name, unchanged=actual == before, before=before, after=actual))
            except (OSError, ValueError) as error:
                checks.append(dict(name=name, unchanged=False, error=str(error)))
        try:
            audit()
            checks.append(dict(name='package_and_shared_inventory', unchanged=True))
        except (O.Failure, OSError, ValueError, KeyError, TypeError) as error:
            checks.append(dict(name='package_and_shared_inventory', unchanged=False, error=str(error)))
        result = dict(status='PASS' if all(c['unchanged'] for c in checks) else 'FAIL', checks=checks)
        save(self.root / 'FINAL-IDENTITIES.json', result)
        return result

    def finish(self):
        O.need(self.check_identities()['status'] == 'PASS', 'final identity checks failed')
        save(self.root / 'RESULT.json', dict(status='PASS', groups=self.groups, rows=len(self.rows),
            commands=self.runner.records, performance_metrics_collected=False,
            exclusions=self.m['exclusions'], historical_captures_reexecuted=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'gate'))
    parser.add_argument('--tools', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--groups', default=','.join(GROUPS))
    args = parser.parse_args()
    gate = None
    try:
        manifest = audit()
        if args.mode == 'audit':
            print('word fixture integrity: PASS (no external tools executed)'); return 0
        O.need(args.tools is not None and args.out is not None, '--tools and --out required')
        gate = Gate(args, manifest)
        for name in GROUPS:
            if name in gate.groups: getattr(gate, name + '_group')()
        gate.finish(); print('word conformance: PASS'); return 0
    except (O.Failure, O.Inconclusive, OSError, ValueError, KeyError, TypeError) as error:
        if gate is not None:
            save(gate.root / 'RESULT.json', dict(status='INCONCLUSIVE' if isinstance(error, O.Inconclusive) else 'FAIL',
                reason=str(error), completed_rows=gate.rows, commands=gate.runner.records,
                final_identities=gate.check_identities(), performance_metrics_collected=False))
        print(str(error), file=sys.stderr); return 1


if __name__ == '__main__':
    sys.exit(main())
