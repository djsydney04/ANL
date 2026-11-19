"""Check committed fixture bytes and identities; never execute native artifacts."""
from pathlib import Path
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
FORMAL = ROOT.parents[1]
MODULES = [
    'NativeByteWordsLiterals', 'NativeUartFenceCertificate',
    'NativeUartByteCertificates', 'NativeUartFenceRestoration',
]
AUDIT = 'NativeUartFixtureAudit'
PAYLOADS = ['core.json', 'mir.json', 'program.c', 'entry.S', 'link.ld', 'manifest.json']
DATA = ['authored.anl', *PAYLOADS, 'selected-text.bin', 'report-projection.json']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def data(name, limit=1 << 20):
    path = ROOT / name
    require(path.is_file() and not path.is_symlink(), 'missing or linked fixture: ' + name)
    require(path.stat().st_size <= limit, 'oversized fixture: ' + name)
    return path.read_bytes()


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def obj(name):
    return json.loads(data(name), object_pairs_hook=pairs)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def indexed(rows, key):
    result = {row[key]: row for row in rows}
    require(len(result) == len(rows), 'duplicate ' + key)
    return result


def check_wiring():
    expected = {name + '.lean' for name in MODULES + [AUDIT]}
    actual = {str(path.relative_to(ROOT)) for path in ROOT.rglob('*.lean')}
    require(actual == expected, 'fixture Lean inventory differs')
    listed = (FORMAL / 'native-uart-fixture-modules.txt').read_text().splitlines()
    require(listed == MODULES, 'fixture replay order differs')
    lake = (FORMAL / 'lakefile.toml').read_text()
    blocks = re.findall(r'^\[\[lean_lib\]\]\n(.*?)(?=^\[\[|\Z)', lake, re.M | re.S)
    chosen = [block for block in blocks if re.search(r'^name = "NativeUartFixtures"$', block, re.M)]
    require(len(chosen) == 1, 'missing or duplicate fixture library')
    fields = {}
    for line in chosen[0].splitlines():
        if line.strip():
            key, value = line.split(' = ', 1)
            require(key not in fields, 'duplicate fixture library field')
            fields[key] = ast.literal_eval(value)
    require(fields == dict(name='NativeUartFixtures', srcDir='fixtures/native-uart', roots=MODULES),
            'fixture library configuration differs')
    defaults = re.findall(r'^defaultTargets = (\[.*\])$', lake, re.M)
    require(len(defaults) == 1 and ast.literal_eval(defaults[0]).count('NativeUartFixtures') == 1,
            'fixture target must build by default')
    for name in expected:
        source = data(name).decode()
        require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe|partial)\b',
                              source, re.M), 'prohibited fixture declaration: ' + name)


def main():
    check_wiring()
    fixture = obj('fixture.json')
    require(fixture['schema'] == 'anl-native-uart-literal-fixture-v1', 'fixture schema')
    require(fixture['data_kind'] == 'seven_complete_selected_bodies_concatenated_not_elf'
            and fixture['word_encoding'] == 'little-endian-u32', 'fixture encoding')
    files = indexed(fixture['files'], 'path')
    require(set(files) == set(DATA), 'data file inventory differs')
    for name, record in files.items():
        raw = data(name)
        require(set(record) == {'path', 'bytes', 'sha256'} and len(raw) == record['bytes']
                and sha(raw) == record['sha256'], 'fixture hash differs: ' + name)
    proofs = indexed(fixture['proof_sources'], 'path')
    require(set(proofs) == {module + '.lean' for module in MODULES}, 'proof source inventory differs')
    for name, record in proofs.items():
        raw = data(name)
        require(set(record) == {'path', 'bytes', 'sha256'} and len(raw) == record['bytes']
                and sha(raw) == record['sha256'], 'proof source hash differs: ' + name)
    expected_files = set(DATA + ['fixture.json', 'check_fixture.py']) | {m + '.lean' for m in MODULES + [AUDIT]}
    require({p.name for p in ROOT.iterdir()} == expected_files, 'unexpected fixture entry')
    forbidden_paths = [b'/' + b'Users/', b'/' + b'home/', b'.git/' + b'apl-internal']
    for name in expected_files:
        require(not any(marker in data(name) for marker in forbidden_paths), 'private path in ' + name)
    manifest = obj('manifest.json')
    require(manifest['input']['bytes'] == len(data('authored.anl'))
            and manifest['input']['sha256'] == sha(data('authored.anl')), 'source/payload join differs')
    artifacts = manifest['artifacts']
    require({row['path'] for row in artifacts.values()} == set(PAYLOADS) - {'manifest.json'},
            'generated artifact inventory differs')
    for row in artifacts.values():
        require(row == files[row['path']], 'generated payload hash differs')
    require(not re.search(r'^\s*import\b', data('authored.anl').decode(), re.M), 'unexpected source import')
    literals = data('NativeByteWordsLiterals.lean').decode()
    headers = re.findall(r'^theorem decode_word_([0-9]+) :\s*\n\s*decode ⟨(0x[0-9a-f]+), by decide⟩ =', literals, re.M)
    literal_map = {int(number): int(raw, 16) for number, raw in headers}
    declared = re.findall(r'^theorem ([A-Za-z0-9_]+)', literals, re.M)
    require(len(headers) == len(literal_map) == len(declared) == 92
            and set(declared) == {'decode_word_' + str(n) for n in literal_map}, 'literal header inventory differs')
    raw = data('selected-text.bin')
    require(len(raw) == fixture['byte_count'] == 368 and fixture['word_count'] == 92, 'selected byte count')
    leaves = fixture['leaves']
    require(len(leaves) == 7 and len(indexed(leaves, 'primitive')) == 7
            and len(indexed(leaves, 'contribution')) == 7, 'leaf identity inventory differs')
    report = obj('report-projection.json')
    require(report['schema'] == 'anl-native-uart-report-projection-v1'
            and report['kind'] == 'selected_fields_of_retained_report_not_new_execution', 'projection schema')
    require(report['original_report'] == fixture['historical_report'], 'historical report identity differs')
    require(set(report['footprint_capabilities']) == {
                'argument_result_provenance_established', 'source_correspondence_established',
                'handler_calls_established', 'handler_stack_bound_established', 'delivery_established',
                'nested_fault_safety_established', 'formal_native_correspondence', 'native_admitted'}
            and set(report['byte_capabilities']) == {'abi_extension_bits_established',
                'source_correspondence_established', 'handler_calls_established', 'native_admitted'}
            and all(value is False for value in report['footprint_capabilities'].values())
            and all(value is False for value in report['byte_capabilities'].values())
            and report['source_native_producer_established'] is False, 'capability claim changed')
    identities = indexed(report['identities'], 'primitive')
    reported = indexed(report['leaves'], 'primitive')
    relations = indexed(report['byte_relations'], 'primitive')
    io = indexed(report['io'], 'word')
    returns = indexed(report['return_locations'], 'word')
    require(all(len(table) == 7 for table in [identities, reported, relations, io, returns]), 'projection row count')
    primitives = indexed(manifest['primitives'], 'id')
    position = 0
    words = {}
    for leaf in leaves:
        body = leaf['words']
        require(bool(body), 'empty leaf body')
        require(leaf['effect_word'] in {word['word_id'] for word in body}, 'effect outside its leaf body')
        require(leaf['fixture_offset'] == position and leaf['size'] == len(body) * 4
                and leaf['object_text_relocations'] == [], 'body layout differs')
        start = position
        for index, word in enumerate(body):
            require(word['word_id'] not in words, 'duplicate word ID')
            require(word['fixture_offset'] == position and word['pc'] == leaf['address'] + 4 * index,
                    'word position or PC differs')
            require(word['raw'] == literal_map.get(word['word_id'])
                    == int.from_bytes(raw[position:position + 4], 'little'), 'literal/byte join differs')
            words[word['word_id']] = word
            position += 4
        require(sha(raw[start:position]) == leaf['sha256'], 'body hash differs')
        identity, observed, relation = [table[leaf['primitive']] for table in [identities, reported, relations]]
        require(all(row['contribution'] == leaf['contribution'] for row in [identity, observed, relation]),
                'contribution join differs')
        require(identity['symbol'] == leaf['symbol'] and identity['operation'] == observed['operation'] == leaf['operation'],
                'primitive identity differs')
        primitive = primitives[leaf['primitive']]
        require(primitive['symbol'] == leaf['symbol'] and primitive['artifact'] == 'c'
                and [primitive['range']['start'], primitive['range']['end']] == identity['c_range'], 'generated-C join differs')
        c_body = data('program.c')[identity['c_range'][0]:identity['c_range'][1]]
        require((leaf['symbol'] + '(').encode() in c_body, 'generated-C symbol missing')
        require(observed['effect_word'] == relation['effect_word'] == leaf['effect_word']
                and observed['return_word'] == relation['return_word'] == leaf['return_word'] == body[-1]['word_id'],
                'effect/return identity differs')
        effect = io[leaf['effect_word']]
        ret = returns[leaf['return_word']]
        require(effect['contribution'] == ret['contribution'] == leaf['contribution']
                and effect['pc'] == words[leaf['effect_word']]['pc'] and ret['pc'] == body[-1]['pc'], 'reported site differs')
        require(set(ret) == {'word', 'pc', 'contribution'}, 'return projection adds an unproved claim')
        kind = leaf['operation']['kind']
        expected = {'IoFence': ('Fence', 'FenceAndUnitZero'), 'Read8': ('ReadByte', 'ReadResponseLow8'),
                    'Write8': ('WriteByte', 'WriteArgumentLow8AndUnitZero')}[kind]
        require((effect['kind'], relation['relation']) == expected, 'byte relation differs')
        if kind != 'IoFence':
            require(effect['address'] == identity['address'] and effect['width'] == 1, 'device address differs')
    require(position == 368 and words.keys() == literal_map.keys(), 'selected word coverage differs')
    print('Native UART fixture bytes: PASS (92 words; offline ELF extraction remains external)')


if __name__ == '__main__':
    main()
