#!/usr/bin/env python3
"""Strict report checks for the frozen tuple-verification workload."""
import copy
import hashlib
import json
import re
import subprocess

class Failure(RuntimeError):pass

def need(ok,message):
    if not ok:raise Failure(message)

def strict(data):
    def pairs(xs):
        out={}
        for k,v in xs:
            need(k not in out,'duplicate JSON key '+k);out[k]=v
        return out
    def constant(v):raise Failure('non-JSON constant '+v)
    return json.loads(data,object_pairs_hook=pairs,parse_constant=constant)

def same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def validate_raw_query_digests(report):
    for index,q in enumerate(report['obligations']):
        need(type(q['query']) is str and type(q['query_sha256']) is str,'raw query/digest must be strings')
        actual=hashlib.sha256(q['query'].encode('utf-8')).hexdigest()
        need(q['query_sha256']==actual,f'raw query digest mismatch at obligation {index}')

def raw_digest_selfcheck():
    query='(set-option :timeout 30000)\n(check-sat)\n'
    valid=dict(status='verified',compiler=None,obligations=[dict(query=query,query_sha256=hashlib.sha256(query.encode()).hexdigest())])
    normalized=normalize(valid)
    need(normalized['obligations'][0]['query']!=query,'self-check did not exercise timeout normalization')
    validate_raw_query_digests(normalized)
    invalid=copy.deepcopy(valid);invalid['obligations'][0]['query_sha256']='0'*64
    result=subprocess.CompletedProcess([],0,json.dumps(invalid).encode(),b'')
    checks=(('normalize',lambda:normalize(invalid)),('scalar check_report',lambda:check_report(result,dict(name='raw-digest-selfcheck',status='verified',exit=0))))
    for name,check in checks:
        try:check()
        except Failure as error:need(str(error)=='raw query digest mismatch at obligation 0',name+' rejected for the wrong reason')
        else:raise Failure(name+' silently repaired malformed raw query digest')
    need(invalid['obligations'][0]['query_sha256']=='0'*64 and invalid['obligations'][0]['query']==query,'self-check input was mutated')
    return dict(valid_raw_digest='accepted',invalid_raw_digest='rejected',entrypoints=[name for name,_ in checks])

def normalize(report):
    validate_raw_query_digests(report)
    result=copy.deepcopy(report)
    if result.get('compiler'):
        for key in ('executable','executable_path_bytes_hex','sha256'):
            need(key in result['compiler'],'missing compiler field '+key);result['compiler'][key]='<compiler identity>'
    for q in result['obligations']:
        q['query']=re.sub(r'\(set-option :timeout [0-9]+\)','(set-option :timeout REMAINING)',q['query'])
        q['query_sha256']=hashlib.sha256(q['query'].encode()).hexdigest()
    return result

def sexps(text):
    stack=[];out=[]
    for token in re.findall(r';[^\n]*|"(?:[^"]|"")*"|[()]|[^\s()]+',text):
        if token.startswith(';'):continue
        if token=='(':stack.append([])
        elif token==')':
            need(bool(stack),'unbalanced SMT close');v=stack.pop();(stack[-1] if stack else out).append(v)
        else:(stack[-1] if stack else out).append(token)
    need(not stack,'unbalanced SMT open');return out

def layout(ty):
    if isinstance(ty,str):need(ty in ('i64','bool','unit'),'invalid scalar type');return [ty]
    need(type(ty) is dict and list(ty)==['tuple'],'invalid product type');xs=ty['tuple']
    need(type(xs) is list and 1<=len(xs)<=8 and all(type(t) is str and t in ('i64','bool','unit') for t in xs),'invalid product shape');return xs

def product_metadata(report,case):
    need(report['schema']=='anl-verify-v3' and report['verification_revision']=='anl-flat-products-verify-v1','product route/revision')
    need(report['trust']=='smt-trusted','trust must remain smt-trusted')
    if case['status']=='unsupported':
        need(report['solver'] is None and report['compiler'] is None and report['obligations']==[],'pre-tool rejection performed tool work');return
    need(report['scope']['termination_proved'] is False and report['scope']['native_correctness'] is False,'unsupported proof claim')
    need(report['scope']['fragment']=='invariant_flat_products_acyclic','wrong scope')
    need(same(report['parameter_layout'],dict(order='source_parameter_then_field',unit_slots='reserved_without_smt_variable',head_logical_identity='initial_logical_bound_plus_head_index_minus_head_display_start')),'parameter layout policy')
    need(same(report['loop_policy'],dict(fresh_head='all_visible_mutable_non_unit_fields',query_grouping='exact_guarded_conjunction',head_models='abstract_mathematical_assignments')),'loop policy')
    functions={f['id']:f for f in report['functions']};need(len(functions)==len(report['functions']),'duplicate function ids')
    expansions={e['id']:e for e in report['expansions']};need(len(expansions)==len(report['expansions']),'duplicate expansion ids')
    parameter={}
    for fid,f in functions.items():
        offset=0;manifest=[]
        for i,ty in enumerate(f['parameter_types']):
            for k,t in enumerate(layout(ty)):
                origin=dict(kind='parameter',index=i,logical_id=offset+k)
                if type(ty) is dict:origin['field_index']=k
                if t!='unit':manifest.append(dict(symbol=f'p{i}_f{k}' if type(ty) is dict else f'p{i}',type=t,origin=origin))
            offset+=len(layout(ty))
        layout(f['result']);parameter[fid]=manifest
        if 'initial_logical_bound' in f:
            need(type(f['initial_logical_bound']) is int and f['initial_logical_bound']==offset and f['parameter_leaf_slots']==offset,'unit-inclusive slot bound')
    heads={}
    for occ in report['loop_occurrences']:
        root=functions[expansions[occ['expansion_id']]['verification_function_id']]
        bindings={b['id']:b for b in functions[occ['source_function_id']]['bindings']}
        for h in occ['head_symbols']:
            name=h['symbol'];need(re.fullmatch(r'h[0-9]+',name) and name not in heads,'duplicate head display')
            index=int(name[1:]);logical=root['initial_logical_bound']+index-root['head_display_start']
            need(type(h['logical_id']) is int and h['logical_id']==logical and logical>=root['initial_logical_bound'],'head logical map')
            binding=bindings[h['binding_id']];need(binding['mutable'] is True,'head of immutable binding')
            field=h.get('field_index');fields=layout(binding['type'])
            if type(binding['type']) is dict:need(type(field) is int and 0<=field<len(fields) and fields[field]==h['type'],'head field provenance')
            else:need(field is None and fields==[h['type']],'scalar head provenance')
            need(h['type']!='unit','unit head allocated')
            origin=dict(kind='loop_head',source_function_id=occ['source_function_id'],loop_node_id=occ['loop_node_id'],expansion_id=occ['expansion_id'],occurrence_id=occ['id'],binding_id=h['binding_id'],logical_id=logical)
            if field is not None:origin['field_index']=field
            heads[name]=dict(symbol=name,type=h['type'],origin=origin)
    need(set(heads)=={f'h{i}' for i in range(len(heads))},'global heads have omissions/reuse')
    for q in report['obligations']:
        need(hashlib.sha256(q['query'].encode()).hexdigest()==q['query_sha256'],'query digest')
        defs={};decls={};assertions=[];requests=[]
        for x in sexps(q['query']):
            if x[0]=='define-fun':need(x[1] not in defs,'duplicate formula node');defs[x[1]]=x[4]
            elif x[0]=='declare-const':need(x[1] not in decls,'duplicate SMT declaration');decls[x[1]]=x[2]
            elif x[0]=='assert':assertions.append(x[1])
            elif x[0]=='get-value':requests.append(x[1])
        need(len(assertions)==1,'wrong assertion count')
        todo=[assertions[0]];visited=set();dependent=set()
        while todo:
            x=todo.pop()
            if isinstance(x,list):todo.extend(x)
            elif re.fullmatch(r'n[0-9]+',x):
                need(x in defs,'undefined formula node')
                if x not in visited:visited.add(x);todo.append(defs[x])
            elif re.fullmatch(r'h[0-9]+',x):dependent.add(x)
        manifest=parameter[q['function_id']]+[heads[h] for h in sorted(dependent,key=lambda h:int(h[1:]))]
        need(same(q['model_symbols'],manifest),'parameter/head leaf manifest mismatch')
        for m in manifest:need(decls.get(m['symbol'])==('Int' if m['type']=='i64' else 'Bool'),'leaf declaration/sort')
        if requests:need(same(requests,[[m['symbol'] for m in manifest]]),'complete get-value request')
        elif q['solver_status']=='sat':need(not manifest,'missing requested model fields')
        if q['model'] is not None:
            model=q['model'];need(model['replayed'] is False,'model must remain unreplayed');assign=model['assignments'];need(len(assign)==len(manifest),'incomplete assignments')
            for m,a in zip(manifest,assign):
                for k in ('symbol','type','origin'):need(same(a[k],m[k]),'assignment metadata')
                v=a['value']
                if m['type']=='bool':need(type(v) is bool,'Boolean model coerced')
                else:
                    need(type(v) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',v),'integer model encoding');within=-(2**63)<=int(v)<2**63
                    if m['origin']['kind']=='parameter':need(within,'out-of-range parameter')
                    else:need(a['within_machine_range'] is within,'head range annotation')
    if case.get('no_symbols'):need(not heads and all(not q['model_symbols'] for q in report['obligations']),'all-unit fields created symbols')
    if case.get('no_head_symbols'):need(not heads,'unit heads allocated')
    if 'head_limit' in case:need(len(heads)==case['head_limit'],'incorrect head limit boundary')
    if 'query_count' in case:need(len(report['obligations'])==case['query_count'],'incorrect query count boundary')
    if report.get('resources'):
        limits=dict(symbolic_work=1000000,arena_nodes=100000,head_symbols=4096,pending_queries=1024)
        for key,cap in limits.items():need(type(report['resources'][key]) is int and 0<=report['resources'][key]<=cap,'resource ceiling '+key)
        need(report['resources']['head_symbols']==len(heads),'resource head count differs')

def check_report(result,case,product=False):
    report=strict(result.stdout);validate_raw_query_digests(report)
    need(result.returncode==case['exit'],f"{case['name']}: exit {result.returncode} != {case['exit']}")
    need(report['status']==case['status'],f"{case['name']}: status {report['status']}")
    if case.get('failed_kind'):need(any(q['kind']==case['failed_kind'] and q['status']=='failed' for q in report['obligations']),'missing expected failed obligation')
    if case.get('message_contains'):need(case['message_contains'] in report['message'],'wrong limit diagnostic')
    if product:product_metadata(report,case)
    if case.get('spec_only'):need(report['semantic_revision']=='m1-2026-11-16','spec product changed executable revision')
    return report
