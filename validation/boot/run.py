#!/usr/bin/env python3
"""Finite boot source/Core admission checks; no boot execution or native emission."""
from pathlib import Path
import argparse, ast, hashlib, json, os, platform, shlex, sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
MEMORY = HERE.parent / 'memory'
WORDS = HERE.parent / 'words'
sys.path.insert(0, str(MEMORY))
from capture import Runner, save
import oracle as O
sys.path.pop(0)


def identity(path):
    p = Path(path).resolve(strict=True)
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''): h.update(chunk)
    return dict(path=str(p), bytes=p.stat().st_size, sha256=h.hexdigest())


def read(path, limit=8388608):
    with Path(path).open('rb') as stream: data = stream.read(limit + 1)
    O.need(len(data) <= limit, 'retained input exceeds bound: ' + str(path))
    return data


def audit():
    seal = O.strict(read(HERE / 'INTEGRITY.json'))
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name != 'INTEGRITY.json'}
    O.need(actual == set(seal['files']), 'boot package inventory differs')
    for name, expected in seal['files'].items():
        p = HERE / name
        O.need(p.is_file() and not p.is_symlink(), 'missing/symlinked package file')
        value = identity(p)
        O.need(value['sha256'] == expected['sha256'] and value['bytes'] == expected['bytes'], 'package bytes differ: ' + name)
    for name, expected in seal['shared'].items():
        value = identity(HERE.parent / name)
        O.need(value['sha256'] == expected['sha256'] and value['bytes'] == expected['bytes'], 'shared capture helper differs: ' + name)
    m = O.strict(read(HERE / 'manifest.json'))
    O.need(m['schema'] == 'anl-boot-validation-corpus-v1', 'corpus schema')
    O.need(len(m['source']) == 8 and len(m['raw']) == 8, 'reviewed corpus inventory')
    for row in m['source'] + m['raw']:
        O.need(identity(HERE / row['path'])['sha256'] == row['sha256'], 'fixture identity differs')
    ast.parse((HERE / 'run.py').read_text(), filename=str(HERE / 'run.py'))
    return m


class Gate:
    def __init__(self, args, manifest):
        self.m, self.rows = manifest, []
        self.root = args.out.resolve()
        O.need(not self.root.exists() and HERE not in self.root.parents, 'fresh output directory required')
        self.record = identity(args.tools)
        records = O.strict(read(args.tools))
        O.keys(records, ('schema', 'tools'))
        O.need(records['schema'] == 'anl-boot-validation-tools-v1', 'tool record schema')
        O.keys(records['tools'], ('rust', 'evidence', 'raw'))
        self.tools, self.identities, self.provenance = {}, {}, {}
        for role, configuration in [('rust', 'default'), ('evidence', 'memory-evidence'), ('raw', 'formal')]:
            row = records['tools'][role]
            O.keys(row, ('path', 'sha256', 'bytes', 'configuration', 'source_manifest'))
            actual = identity(row['path'])
            O.need(os.access(actual['path'], os.X_OK), 'tool is not executable: ' + role)
            O.need(actual['sha256'] == row['sha256'] and actual['bytes'] == row['bytes'], 'tool bytes differ: ' + role)
            O.need(row['configuration'] == configuration, 'tool configuration differs: ' + role)
            O.keys(row['source_manifest'], ('path', 'sha256'))
            provenance = identity(row['source_manifest']['path'])
            O.need(provenance['sha256'] == row['source_manifest']['sha256'], 'build provenance differs: ' + role)
            self.tools[role], self.identities[role], self.provenance[role] = Path(actual['path']), actual, provenance
        O.need(self.provenance['rust']['sha256'] == self.provenance['evidence']['sha256'], 'mixed compiler build family')
        self.root.mkdir(parents=True, exist_ok=False)
        self.runner = Runner(self.root, manifest)
        self.package = identity(HERE / 'INTEGRITY.json')
        self.spy = self.root / 'tool-spy'
        self.spy.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' + shlex.quote(str(MEMORY / 'tool_spy.py')) + ' "$@"\n')
        self.spy.chmod(0o700)
        self.spy_log = self.root / 'forbidden-tool-startup'
        self.env = dict(CC=str(self.spy), ANL_CORPUS_SPY_LOG=str(self.spy_log),
                        ANL_MEMORY_TRACE=str(self.root / 'uncreated-trace'), ANL_MEMORY_REPLAY=str(self.root / 'unread-replay'))
        save(self.root / 'IDENTITY.json', dict(tool_record=self.record, tools=self.identities,
            source_manifests=self.provenance, package=self.package, python=identity(sys.executable),
            host=dict(system=platform.system(), machine=platform.machine()),
            provenance_claim='Explicit build records and actual binary/input/output hashes; build and proof qualification remain separate.',
            performance_metrics_collected=False))

    def call(self, label, argv, inputs=(), env=None):
        expected = [identity(argv[0]), *[identity(p) for p in inputs]]
        name = f'{self.runner.count + 1:04d}-{label}'
        pending = self.root / 'command-bindings' / (name + '.json')
        folder = self.root / 'commands' / name
        binding = dict(state='before_launch', expected=expected)
        save(pending, binding)
        try:
            result = self.runner.run(label, argv, self.env if env is None else env)
        finally:
            checks = []
            for before in expected:
                try:
                    after = identity(before['path'])
                    checks.append(dict(before=before, after=after, unchanged=before == after))
                except (OSError, ValueError) as error:
                    checks.append(dict(before=before, unchanged=False, error=str(error)))
            binding.update(state='after_attempt', checks=checks, unchanged=all(c['unchanged'] for c in checks))
            save(pending, binding)
            if folder.is_dir(): save(folder / 'bindings.json', binding)
        O.need(binding['unchanged'], 'tool/input changed during command')
        O.need(not self.spy_log.exists(), 'unsupported route invoked external tool')
        return result

    def row(self, name):
        self.rows.append(dict(case=name, status='PASS'))
        save(self.root / 'ROWS.json', self.rows)

    def formal(self, label, path, expected):
        r = self.call(label + '-formal', [self.tools['raw'], path], [path])
        doc = O.strict(r['stdout']); O.keys(doc, ('raw_valid', 'reason'))
        O.need(r['exit'] == expected and r['stderr'] == b'', 'formal admission status')
        O.need(type(doc['raw_valid']) is bool and doc['raw_valid'] is (expected == 0), 'formal raw_valid')
        O.need(type(doc['reason']) is str and len(doc['reason'].encode('utf-8')) <= 1024 and (doc['reason'] == '') == (expected == 0), 'formal reason')
        O.need(r['stdout'].endswith(b'\n') and r['stdout'].count(b'\n') == 1, 'formal response framing')

    def rust_raw(self, label, path, expected):
        r = self.call(label + '-rust', [self.tools['rust'], 'eval-core', path, '--fuel', '0'], [path])
        tag = {7: 'unsupported_boot_operation', 1: 'invalid_ir', 3: 'resource_limit'}[expected]
        O.need(r['exit'] == expected and r['stdout'] == (json.dumps(dict(outcome=tag), separators=(',', ':')) + '\n').encode(), 'Rust raw status/protocol')
        O.need(bool(r['stderr']) == (expected != 7), 'Rust raw diagnostic channel')

    def source(self):
        self.exports = {}
        for row in self.m['source']:
            path = HERE / row['path']; name = row['name']
            r = self.call(name + '-check', [self.tools['rust'], 'check', path], [path])
            O.need(r['exit'] == row['exit'] and not r['stdout'] and bool(r['stderr']) == (row['exit'] != 0), 'source admission')
            if row['exit'] == 0:
                dumped = self.call(name + '-dump', [self.tools['rust'], 'dump-core', path], [path])
                O.need(dumped['exit'] == 0 and not dumped['stderr'] and dumped['stdout'].endswith(b'\n') and len(dumped['stdout']) <= 1048576, 'actual Core export')
                core = self.root / 'exports' / (name + '.json'); core.parent.mkdir(exist_ok=True); core.write_bytes(dumped['stdout'])
                self.exports[name] = core
                doc = O.strict(dumped['stdout']); oracle = self.m['source_oracles'][name]
                definitions = [f for f in doc['functions'] if f['kind'] == 'defined']
                primitives = [f for f in doc['functions'] if f['kind'] == 'primitive']
                O.need(doc['schema'] == 'anl-boot-core-v1' and doc['semantic_revision'] == 'anl-boot-rv64-virt-v1' and doc['ordinary_semantic_revision'] == 'anl-words-v1', 'Core revisions')
                O.need(len(definitions) == oracle['defined'] and [f['id'] for f in doc['functions']] == list(range(len(doc['functions']))), 'defined/primitive IDs')
                if 'primitive_file' in oracle:
                    O.need(O.same(primitives, O.strict(read(HERE / oracle['primitive_file']))), 'independent normal primitive table')
                else: O.need([p['operation']['tag'] for p in primitives] == oracle['tags'], 'primitive preorder')
                if name == 'nested-write-read':
                    outer = definitions[0]['body']['body']['body']['body']['value']
                    O.need(outer['function'] == oracle['outer_write_id'] and outer['arguments'][0]['function'] == oracle['nested_read_id'], 'outer primitive ID precedes operand ID')
                self.formal(name, core, 0)
                self.rust_raw(name, core, 7)
                evidence = self.call(name + '-evidence-dump', [self.tools['evidence'], 'dump-core', path], [path])
                O.need(evidence['exit'] == 0 and not evidence['stderr'] and evidence['stdout'] == dumped['stdout'], 'compiler configurations changed boot Core')
            self.row('source:' + name)

    def raw(self):
        for row in self.m['raw']:
            path = HERE / row['path']
            # Both readers consume these exact bytes, including malformed spellings.
            self.formal(row['name'], path, row['exit'])
            self.rust_raw(row['name'], path, 7 if row['exit'] == 0 else row['exit'])
            self.row('raw:' + row['name'])
        base = read(HERE / 'raw/minimal-valid.json')
        for row in self.m['boundaries']:
            if row['kind'] == 'pad':
                O.need(len(base) <= row['bytes'], 'base fits byte-boundary recipe')
                data = base + b' ' * (row['bytes'] - len(base))
            else:
                n = row['arrays']
                data = base.rstrip()[:-1] + b',"extra":' + b'[' * n + b'0' + b']' * n + b'}\n'
            path = self.root / 'boundaries' / (row['name'] + '.json'); path.parent.mkdir(exist_ok=True); path.write_bytes(data)
            self.formal(row['name'], path, row['formal_exit'])
            self.rust_raw(row['name'], path, row['rust_exit'])
            self.row('boundary:' + row['name'])

    def controls(self):
        path = HERE / 'source/minimal-park.anl'
        report = read(HERE / 'unsupported-verify.json')
        for role in ('rust', 'evidence'):
            for command in ('eval', 'run', 'emit-c', 'emit-boot', 'build', 'verify'):
                args = [self.tools[role], command, path]
                if command == 'eval': args += ['--fuel', '0']
                if command == 'emit-boot': args += ['--out', self.root / 'uncreated-bundle']
                if command == 'build': args += ['--toolchain', self.root / 'unread-lock', '-o', self.root / 'uncreated-image']
                if command == 'verify': args += ['--json', '--solver', self.spy]
                r = self.call(role + '-' + command, args, [path, self.spy, MEMORY / 'tool_spy.py'])
                O.need(r['exit'] == 7, 'checked unsupported route status')
                if command == 'verify': O.need(r['stdout'] == report and not r['stderr'], 'exact unsupported report/proof flags')
                else:
                    state = 'implemented' if command in ('emit-boot', 'build') else 'supported'
                    O.need(not r['stdout'] and r['stderr'] == f'unsupported_boot_operation: {command} is not {state} for rv64-virt-sbi-v1\n'.encode(), 'unsupported diagnostic')
                self.row('control:' + role + ':' + command)
        for name in ('uncreated-bundle', 'uncreated-image', 'unread-lock', 'unread-replay', 'uncreated-trace'):
            O.need(not (self.root / name).exists(), 'unsupported route created an artifact')
        readonly = self.root / 'readonly-output'; readonly.write_bytes(b'unchanged')
        core = self.exports['minimal-park']; helper = WORDS / 'closed_stdout.py'
        for role, args in [('rust', ['eval-core', core]), ('raw', [core])]:
            r = self.call(role + '-readonly-stdout', [sys.executable, helper, readonly, self.tools[role], *args],
                          [helper, readonly, self.tools[role], core])
            O.need(r['exit'] == 4 and not r['stdout'] and bool(r['stderr']) and readonly.read_bytes() == b'unchanged', 'actual readonly stdout failure')
            self.row('control:' + role + ':readonly-stdout')

    def check_identities(self):
        checks = []
        for before in [self.record, self.package, *self.identities.values(), *self.provenance.values()]:
            try:
                after = identity(before['path']); checks.append(dict(before=before, after=after, unchanged=before == after))
            except (OSError, ValueError) as error: checks.append(dict(before=before, unchanged=False, error=str(error)))
        try: audit(); checks.append(dict(package_and_shared_inventory=True, unchanged=True))
        except (O.Failure, OSError, ValueError, KeyError, TypeError) as error: checks.append(dict(package_and_shared_inventory=False, unchanged=False, error=str(error)))
        result = dict(status='PASS' if all(c['unchanged'] for c in checks) else 'FAIL', checks=checks)
        save(self.root / 'FINAL-IDENTITIES.json', result)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'gate'))
    parser.add_argument('--tools', type=Path)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args(); gate = None
    try:
        manifest = audit()
        if args.mode == 'audit': print('boot corpus integrity: PASS (no external tools executed)'); return 0
        O.need(args.tools is not None and args.out is not None, '--tools and --out required')
        gate = Gate(args, manifest)
        gate.source(); gate.raw(); gate.controls()
        O.need(gate.check_identities()['status'] == 'PASS', 'final identity checks failed')
        save(gate.root / 'RESULT.json', dict(status='PASS', rows=gate.rows, commands=gate.runner.records,
            exclusions=manifest['exclusions'], performance_metrics_collected=False))
        print('boot source/Core conformance: PASS'); return 0
    except (O.Failure, OSError, ValueError, KeyError, TypeError) as error:
        if gate is not None:
            save(gate.root / 'RESULT.json', dict(status='INCONCLUSIVE' if isinstance(error, O.Inconclusive) else 'FAIL',
                reason=str(error), rows=gate.rows, commands=gate.runner.records,
                final_identities=gate.check_identities(), performance_metrics_collected=False))
        print(str(error), file=sys.stderr); return 1


if __name__ == '__main__':
    sys.exit(main())
