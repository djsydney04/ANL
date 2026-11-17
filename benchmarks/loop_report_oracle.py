#!/usr/bin/env python3
"""Independent report oracle, reconstructing dependencies from recorded SMT.

Production must maintain explicit operand links. This review oracle deliberately
uses a different representation: parse the external SMT transcript and traverse
its actual named definitions, then compare the report's link-derived manifest.
It verifies record consistency and exact conjunction membership, not source-to-VC
soundness or any solver result.
"""
from pathlib import Path
import argparse
from collections import defaultdict
import hashlib
import json
import re


def sexps(text):
    tokens = re.findall(r';[^\n]*|"(?:[^"]|"")*"|[()]|[^\s()]+', text)
    stack, result = [], []
    for token in tokens:
        if token.startswith(';'):
            continue
        if token == '(':
            stack.append([])
        elif token == ')':
            assert stack, 'unbalanced close'
            value = stack.pop()
            (stack[-1] if stack else result).append(value)
        else:
            (stack[-1] if stack else result).append(token)
    assert not stack, 'unbalanced open'
    return result


def atoms(term):
    todo = [term]
    while todo:
        value = todo.pop()
        if isinstance(value, list):
            todo.extend(value)
        else:
            yield value


def rendered(query):
    forms = sexps(query['query'])
    definitions, declarations, assertions, requests = {}, {}, [], []
    for form in forms:
        assert isinstance(form, list) and form, form
        if form[0] == 'define-fun' and re.fullmatch(r'n\d+', form[1]):
            assert len(form) == 5 and form[2] == [] and form[1] not in definitions, form
            definitions[form[1]] = form[4]
        elif form[0] == 'declare-const':
            assert len(form) == 3 and form[1] not in declarations, form
            declarations[form[1]] = form[2]
        elif form[0] == 'assert':
            assert len(form) == 2, form
            assertions.append(form[1])
        elif form[0] == 'get-value':
            assert len(form) == 2, form
            requests.append(form[1])
    assert len(assertions) == 1, assertions
    return definitions, declarations, assertions[0], requests


def dependencies(definitions, term):
    todo, visited, heads = [term], set(), set()
    while todo:
        item = todo.pop()
        if isinstance(item, list):
            todo.extend(item)
        elif re.fullmatch(r'n\d+', item):
            assert item in definitions, ('undefined node', item)
            if item not in visited:
                visited.add(item)
                todo.append(definitions[item])
        elif re.fullmatch(r'h\d+', item):
            heads.add(item)
    return heads


def conjunction_members(definitions, term):
    """Expand only conjunction/true nodes; keep actual implication IDs atomic."""
    todo, result = [term], []
    while todo:
        item = todo.pop()
        resolved = definitions.get(item, item) if isinstance(item, str) else item
        if resolved == 'true':
            continue
        if isinstance(resolved, list) and resolved and resolved[0] == 'and':
            todo.extend(reversed(resolved[1:]))
        else:
            result.append(item)
    return result


def check_report(report):
    assert report['schema'] == 'apl-verify-v1'
    assert report['verification_revision'] == 'apl-loop-verify-v1'
    assert report['trust'] == 'smt-trusted'
    assert report['scope']['termination_proved'] is False
    assert report['scope']['native_correctness'] is False
    assert report['source_loop_metadata_complete'] is True
    assert report['loop_policy'] == {
        'fresh_head': 'all_visible_mutable_non_unit',
        'query_grouping': 'exact_guarded_conjunction',
        'head_models': 'abstract_mathematical_assignments',
    }
    functions = {f['id']: f for f in report['functions']}
    assert len(functions) == len(report['functions'])
    expansions = {e['id']: e for e in report['expansions']}
    assert list(expansions) == list(range(len(expansions)))
    occurrences = {o['id']: o for o in report['loop_occurrences']}
    assert list(occurrences) == list(range(len(occurrences)))
    heads, source_loops, bindings = {}, {}, {}
    for fid, function in functions.items():
        bindings[fid] = {b['id']: b for b in function['bindings']}
        assert list(bindings[fid]) == list(range(len(bindings[fid])))
        for binding in function['bindings']:
            assert binding['parent'] is None or binding['parent'] < binding['id']
        source_loops[fid] = {l['node_id']: l for l in function['loops']}
        assert list(source_loops[fid]) == sorted(source_loops[fid])
        assert function['invariant_clauses'] == sum(len(l['clauses']) for l in function['loops'])
        for loop in function['loops']:
            assert [c['index'] for c in loop['clauses']] == list(range(len(loop['clauses'])))
            assert loop['clauses'], ('unannotated loop', fid, loop['node_id'])
    for expansion in expansions.values():
        assert expansion['verification_function_id'] in functions
        assert expansion['source_function_id'] in functions
        parent = expansion['parent_expansion_id']
        if parent is None:
            assert expansion['call_node_id'] is None
            assert expansion['verification_function_id'] == expansion['source_function_id']
        else:
            assert parent < expansion['id']
            assert expansion['call_node_id'] is not None
            assert expansions[parent]['verification_function_id'] == expansion['verification_function_id']
    for occurrence in occurrences.values():
        expansion = expansions[occurrence['expansion_id']]
        fid = occurrence['source_function_id']
        assert fid == expansion['source_function_id']
        source = source_loops[fid][occurrence['loop_node_id']]
        assert occurrence['location'] == source['location']
        context, binding_id = [], source['head_binding']
        while binding_id is not None:
            binding = bindings[fid][binding_id]
            context.append(binding)
            binding_id = binding['parent']
        expected_bindings = {b['id'] for b in context if b['mutable'] and b['type'] != 'unit'}
        observed_bindings = {h['binding_id'] for h in occurrence['head_symbols']}
        assert observed_bindings == expected_bindings, ('head scope', occurrence, expected_bindings)
        assert len(observed_bindings) == len(occurrence['head_symbols'])
        for head in occurrence['head_symbols']:
            symbol = head['symbol']
            assert symbol not in heads and re.fullmatch(r'h\d+', symbol), symbol
            assert head['type'] in ('i64', 'bool')
            assert head['type'] == bindings[fid][head['binding_id']]['type']
            heads[symbol] = {
                'symbol': symbol, 'type': head['type'], 'origin': {
                    'kind': 'loop_head', 'source_function_id': fid,
                    'loop_node_id': occurrence['loop_node_id'],
                    'expansion_id': occurrence['expansion_id'],
                    'occurrence_id': occurrence['id'], 'binding_id': head['binding_id'],
                }}
    assert set(heads) == {f'h{i}' for i in range(len(heads))}, 'global fresh IDs reused or skipped'
    per_function = defaultdict(list)
    for query in report['obligations']:
        per_function[query['function_id']].append(query)
    count_checks = 0
    for fid, function in functions.items():
        queries = per_function[fid]
        root_expansions = [e for e in expansions.values() if e['verification_function_id'] == fid and e['parent_expansion_id'] is None]
        assert len(root_expansions) == 1, (fid, root_expansions)
        expected = [('precondition_defined', i) for i in range(function['requires'])]
        expected += [('precondition_satisfiable', None), ('body_safe', None)]
        for occurrence in occurrences.values():
            if expansions[occurrence['expansion_id']]['verification_function_id'] != fid:
                continue
            clauses = source_loops[occurrence['source_function_id']][occurrence['loop_node_id']]['clauses']
            for kind in ('loop_invariant_initialized', 'loop_invariant_preserved'):
                expected += [(kind, (occurrence['id'], c['index'])) for c in clauses]
        expected += [('postcondition', i) for i in range(function['ensures'])]
        assert len(queries) == len(expected), ('query partition length', fid, len(queries), expected)
        identifiers = []
        declared_heads = {symbol for symbol, head in heads.items()
                          if expansions[head['origin']['expansion_id']]['verification_function_id'] == fid}
        parameter_manifest = [{'symbol': f'p{i}', 'type': ty, 'origin': {'kind': 'parameter', 'index': i}}
                              for i, ty in enumerate(function['parameter_types']) if ty != 'unit']
        for query, (kind, index) in zip(queries, expected):
            assert query['kind'] == kind, ('query order', fid, kind, query['kind'])
            assert hashlib.sha256(query['query'].encode()).hexdigest() == query['query_sha256']
            definitions, declarations, assertion, requests = rendered(query)
            assert assertion == query['query_assertion'], ('assertion metadata', query['id'])
            assert set(s for s in declarations if s.startswith('h')) == declared_heads
            reached = dependencies(definitions, assertion)
            expected_manifest = parameter_manifest + [heads[h] for h in sorted(reached, key=lambda x: int(x[1:]))]
            assert query['model_symbols'] == expected_manifest, ('SMT/manifest dependency mismatch', fid, query['id'], reached)
            if requests:
                assert requests == [[s['symbol'] for s in expected_manifest]], ('model request', query['id'])
            elif query['solver_status'] == 'sat':
                assert not expected_manifest, ('missing model request', query['id'])
            if query['model'] is not None:
                assert query['model']['replayed'] is False
                assignments = query['model']['assignments']
                assert len(assignments) == len(expected_manifest)
                for entry, assignment in zip(expected_manifest, assignments):
                    for field in ('symbol', 'type', 'origin'):
                        assert assignment[field] == entry[field]
                    assert 'parameter' not in assignment
                    value = assignment['value']
                    if entry['type'] == 'bool':
                        assert isinstance(value, bool)
                        assert 'within_machine_range' not in assignment
                    else:
                        assert isinstance(value, str) and re.fullmatch(r'-?(0|[1-9][0-9]*)', value)
                        within = -(2**63) <= int(value) < 2**63
                        if entry['origin']['kind'] == 'loop_head':
                            assert assignment['within_machine_range'] is within
                        else:
                            assert within and 'within_machine_range' not in assignment
            checks = query['checks']
            if kind == 'precondition_satisfiable':
                assert not checks and not reached
                assert query['expected_solver_status'] == 'sat'
                continue
            assert query['expected_solver_status'] == 'unsat'
            if kind != 'body_safe':
                assert len(checks) == 1, (kind, checks)
            implication_ids = []
            for check in checks:
                identifiers.append(check['id'])
                expansion = expansions[check['expansion_id']]
                assert expansion['verification_function_id'] == fid
                assert expansion['source_function_id'] == check['source_function_id']
                assert definitions[check['implication']] == ['=>', check['guard'], check['required']], check
                implication_ids.append(check['implication'])
                origin = check['origin']
                if kind == 'body_safe':
                    assert origin['kind'] in ('arithmetic', 'call_preconditions')
                    if origin['kind'] == 'call_preconditions':
                        children = [e for e in expansions.values() if e['parent_expansion_id'] == check['expansion_id'] and e['call_node_id'] == origin['call_node_id']]
                        assert len(children) == 1 and children[0]['source_function_id'] == origin['callee_function_id']
                        assert len(origin['clauses']) == functions[origin['callee_function_id']]['requires']
                        for clause in origin['clauses']:
                            assert clause['defined'] in definitions and clause['truth'] in definitions
                elif kind.startswith('loop_invariant_'):
                    assert origin['kind'] == kind
                    assert (origin['occurrence_id'], origin['clause_index']) == index
                    occurrence = occurrences[origin['occurrence_id']]
                    assert check['expansion_id'] == occurrence['expansion_id']
                    assert origin['loop_node_id'] == occurrence['loop_node_id']
                    source = source_loops[check['source_function_id']][origin['loop_node_id']]
                    assert query['location'] == source['clauses'][origin['clause_index']]['location']
                else:
                    assert origin['kind'] == ('entry_precondition' if kind == 'precondition_defined' else 'postcondition')
                    assert origin['clause_index'] == index
            asserted = definitions[assertion]
            assert isinstance(asserted, list) and len(asserted) == 2 and asserted[0] == 'not', ('non-partition assertion', fid, query['id'], asserted)
            actual_members = conjunction_members(definitions, asserted[1])
            assert actual_members == implication_ids, ('conjunction membership', fid, query['id'], actual_members, implication_ids)
        assert sorted(identifiers) == list(range(len(identifiers))), ('missing/duplicate check ID', fid, identifiers)
        count_checks += len(identifiers)
    return {'functions': len(functions), 'occurrences': len(occurrences),
            'heads': len(heads), 'queries': len(report['obligations']), 'checks': count_checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reports', type=Path, nargs='+')
    args = parser.parse_args()
    results = []
    for path in args.reports:
        report = json.loads(path.read_text())
        results.append(dict(path=str(path), **check_report(report)))
    print(json.dumps({'result': 'PASS', 'reports': results}, indent=2))


if __name__ == '__main__':
    main()
