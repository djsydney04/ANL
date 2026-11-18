"""Deterministic boundary inputs; sizes, hashes, and outcomes are sealed separately."""
import json


def generate(row, here):
    kind = row['generator']
    if kind == 'invalid-utf8':
        return b' ' * (row['target_bytes'] - 1) + b'\xff'
    if kind == 'padding':
        data = (here / row['base']).read_bytes()
        if row['target_bytes'] < len(data):
            raise ValueError('padding target shorter than input')
        return data + b' ' * (row['target_bytes'] - len(data))
    if kind == 'json-depth':
        return b'[' * row['depth'] + b'0' + b']' * row['depth']
    if kind == 'duplicate-plan':
        return b'{"schema":"anl-memory-response-plan-v1","responses":[],"responses":[],"default":"success"}\n'
    if kind == 'casts':
        obj = json.loads((here / 'core/legacy-only-v4.json').read_bytes())
        term = obj['functions'][0]['body']
        for _ in range(row['count']):
            term = dict(tag='convert', ty='i64', mode='checked', target='i64', operand=term)
        obj['functions'][0]['body'] = term
    elif kind == 'mir-branches':
        obj = json.loads((here / 'mir/legacy-only-v4.json').read_bytes())
        condition, value = dict(id=0, ty='bool'), dict(id=1, ty='i64')
        block = dict(instructions=[], **{'yield': value})
        for index in range(row['count']):
            destination = dict(id=index+2, ty='i64')
            op = dict(tag='branch', condition=condition, then=block, **{'else': dict(instructions=[], **{'yield': value})})
            block = dict(instructions=[dict(destination=destination, operation=op)], **{'yield': destination})
        block['instructions'] = [dict(destination=condition, operation=dict(tag='boolean', value=True)),
                                 dict(destination=value, operation=dict(tag='integer', value='42'))] + block['instructions']
        obj['functions'][0].update(body=block, temp_count=row['count']+2)
    elif kind == 'responses':
        responses = ['refused'] * row['count']
        if row.get('invalid_last'): responses[-1] = 'invalid'
        obj = dict(schema='anl-memory-response-plan-v1', responses=responses, default='success')
    elif kind == 'events':
        obj = json.loads((here / 'trace/view-success.json').read_bytes())
        events = []
        for n in range(row['count'] // 2):
            site = dict(function=2, heap=0)
            events.extend([dict(kind='empty_open', empty=str(n), site=site), dict(kind='empty_close', empty=str(n), site=site)])
        if row['count'] % 2:
            events.append(dict(kind='empty_open', empty=str(row['count']//2), site=dict(function=2, heap=0)))
            obj['completion'] = dict(kind='trap', trap='invalid_shift')
        obj['events'] = events
    else:
        raise ValueError('unknown boundary generator')
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()
