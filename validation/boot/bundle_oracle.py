"""Read complete emitted bundles; qualify structure and bytes, not target execution."""
from pathlib import Path
import json,re,hashlib

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def strict(b):
 def object_pairs(items):
  out={}
  for k,v in items:
   need(k not in out,'duplicate JSON key');out[k]=v
  return out
 def invalid_constant(value):raise ValueError('non-JSON constant '+value)
 return json.loads(b,object_pairs_hook=object_pairs,parse_constant=invalid_constant)
def keys(value,names):need(type(value)is dict and set(value)==set(names.split()),'exact object fields '+names)
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b
def selected_tail(expr):
 if expr['tag']=='while' and expr['condition']['tag']=='boolean' and expr['condition']['value'] is True and expr['body']['tag']=='unit':return []
 if expr['tag'] in ('let','let_mut'):
  for name,field in [('letValue','value'),('letBody','body')]:
   found=selected_tail(expr[field])
   if found is not None:return [{'edge':name}]+found
 return None
CHILDREN={'mutable_scope':[('mutableBody','body')],'while':[('whileCondition','condition'),('whileBody','body')],'branch':[('branchThen','then'),('branchElse','else')]}
def paths(block,prefix=()):
 for index,ins in enumerate(block['instructions']):
  yield (prefix,index),ins
  for child,field in CHILDREN.get(ins['operation']['tag'],[]):yield from paths(ins['operation'][field],prefix+((index,child),))
def path_key(p):
 keys(p,'blocks instruction')
 need(type(p['instruction'])is int and p['instruction']>=0,'MIR instruction index')
 for b in p['blocks']:
  keys(b,'instruction child');need(type(b['instruction'])is int and b['instruction']>=0,'MIR parent index')
 return tuple((b['instruction'],b['child']) for b in p['blocks']),p['instruction']
def core_at(expr,path):
 edges={'letValue':(['let','let_mut'],'value'),'letBody':(['let','let_mut'],'body'),'whileCondition':(['while'],'condition'),'whileBody':(['while'],'body'),'ifCondition':(['if'],'condition'),'ifThen':(['if'],'then'),'ifElse':(['if'],'else'),'unaryOperand':(['unary'],'operand'),'binaryLeft':(['binary'],'left'),'binaryRight':(['binary'],'right'),'convertOperand':(['convert'],'operand'),'projectOperand':(['project'],'value'),'assignValue':(['assign'],'value')}
 for e in path:
  if e['edge'] in ['callArgument','tupleField']:
   keys(e,'edge index');tag,field={'callArgument':('call','arguments'),'tupleField':('tuple','fields')}[e['edge']];need(expr['tag']==tag,'indexed Core parent');need(type(e['index'])is int and 0<=e['index']<len(expr[field]),'Core child index');expr=expr[field][e['index']]
  else:
   keys(e,'edge');tags,field=edges[e['edge']];need(expr['tag'] in tags,'Core parent constructor');expr=expr[field]
 return expr
def slice_range(r,data):
 keys(r,'start end');a,b=r['start'],r['end'];need(type(a)is int and type(b)is int and 0<=a<b<=len(data),'actual byte range');data[:a].decode();data[:b].decode();return data[a:b]
def function_text(data,start):
 end=start;depth=0;seen=False
 while end<len(data):
  if data[end]=='{':depth+=1;seen=True
  elif data[end]=='}':
   depth-=1
   if seen and depth==0:return data[start:end+2]
  end+=1
 raise ValueError('unterminated C function')
def expected_primitive(row):
 i=row['id'];o=row['operation'];tag=o['tag'];symbol='anl_boot_f'+str(i)
 if tag=='mmio_read8':return f'''static uint8_t {symbol}(void) {{\n    uint64_t value;\n    __asm__ volatile ("lbu %0, 0(%1)" : "=r" (value) : "r" (UINT64_C(268435461)) : "memory");\n    return (uint8_t)value;\n}}\n'''
 if tag=='mmio_write8':return f'''static unsigned char {symbol}(uint8_t value) {{\n    __asm__ volatile ("sb %0, 0(%1)" : : "r" ((uint64_t)value), "r" (UINT64_C({268435456+o['offset']})) : "memory");\n    return 0;\n}}\n'''
 asm={'io_fence':'fence iorw, iorw','csr_clear':'csrci sstatus, 2','csr_write':'csrw sie, zero','install_trap':'csrw stvec, %0'}[tag]
 operands=': : "r" (anl_boot_hardware_entry) : "memory"' if tag=='install_trap' else ': : : "memory"'
 return f'''static unsigned char {symbol}(void) {{\n    __asm__ volatile ("{asm}" {operands});\n    return 0;\n}}\n'''
def expected_entry(role,ident):
 name={'boot':'anl_boot_entry','hardware':'anl_boot_hardware_entry','language':'anl_boot_language_entry'}[role]
 setup={'boot':'    lla sp, __anl_boot_stack_top\n    andi sp, sp, -16\n','hardware':'    csrr a0, scause\n    csrr a1, sepc\n    csrr a2, stval\n    lla sp, __anl_terminal_stack_top\n    andi sp, sp, -16\n','language':'    andi a0, a0, 255\n    lla sp, __anl_terminal_stack_top\n    andi sp, sp, -16\n'}[role]
 return f'.section .text.{name},"ax",@progbits\n.balign 4\n.globl {name}\n.type {name},@function\n{name}:\n{setup}    tail anl_boot_f{ident}\n.size {name}, .-{name}\n'
def check_bundle(folder,source,root):
 names={'core.json','mir.json','program.c','entry.S','link.ld','manifest.json'}
 need({p.name for p in folder.iterdir()}==names,'exact six-file inventory')
 caps=dict(zip(['core.json','mir.json','program.c','entry.S','link.ld','manifest.json'],[1048576,8388608,67108864,1048576,65536,1048576]))
 data={}
 for n in names:
  need((folder/n).is_file() and not(folder/n).is_symlink(),'regular artifact '+n)
  with (folder/n).open('rb') as stream:data[n]=stream.read(caps[n]+1)
  need(len(data[n])<=caps[n] and data[n].endswith(b'\n'),'bounded LF artifact '+n);data[n].decode('utf-8')
 manifest=strict(data['manifest.json']);core=strict(data['core.json']);mir=strict(data['mir.json']);c=data['program.c'].decode()
 for doc,schema in [(core,'anl-boot-core-v1'),(mir,'anl-boot-mir-v1')]:
  keys(doc,'schema semantic_revision ordinary_semantic_revision target_profile image stacks devices entries functions');need(doc['schema']==schema,'Core/MIR schema')
 for key in core.keys()-{'schema','functions'}:need(same(core[key],mir[key]),'Core/MIR metadata '+key)
 need(len(core['functions'])==len(mir['functions']),'Core/MIR declaration count')
 for cf,mf in zip(core['functions'],mir['functions']):
  if cf['kind']=='primitive':need(same(cf,mf),'bodyless primitive row')
  else:
   keys(mf,'kind id name view params result effects body temp_count slot_count resource_count')
   need(all(same(cf[k],mf[k]) for k in ['kind','id','name','view','result','effects']),'defined declaration metadata')
   need(same(cf['params'],[p['ty'] for p in mf['params']]) and type(mf['resource_count'])is int and mf['resource_count']==0,'defined parameter/resource signature')
 keys(manifest,'schema semantic_revision ordinary_semantic_revision target input artifacts functions primitives origins parks abi')
 need([manifest[k] for k in ['schema','semantic_revision','ordinary_semantic_revision','target']]==['anl-boot-bundle-v1','anl-boot-rv64-virt-v1','anl-words-v1','rv64-virt-sbi-v1'],'manifest revisions')
 keys(manifest['input'],'kind bytes sha256');identity=source if source is not None else data['core.json']
 need(manifest['input']==dict(kind='source' if source is not None else 'canonical_core',bytes=len(identity),sha256=sha(identity)),'exact input identity')
 keys(manifest['artifacts'],'core mir c assembly linker')
 for k,n in zip(['core','mir','c','assembly','linker'],['core.json','mir.json','program.c','entry.S','link.ld']):
  keys(manifest['artifacts'][k],'path bytes sha256');need(manifest['artifacts'][k]==dict(path=n,bytes=len(data[n]),sha256=sha(data[n])),'actual artifact identity')
 def span(s):
  if source is None:need(s is None,'raw source spans must be null');return None
  keys(s,'start end');a,b=s['start'],s['end'];need(type(a)is int and type(b)is int and 0<=a<=b<=len(source),'source span');source[:a].decode();source[:b].decode();return source[a:b]
 defined=[f for f in core['functions'] if f['kind']=='defined'];primitive=[f for f in core['functions'] if f['kind']=='primitive']
 need(len(manifest['functions'])==len(defined) and len(manifest['primitives'])==len(primitive),'complete declaration maps')
 for row,f in zip(manifest['functions'],defined):
  keys(row,'id name symbol source_span c_range');need((row['id'],row['name'],row['symbol'])==(f['id'],f['name'],'anl_boot_f'+str(f['id'])),'function mapping');text=slice_range(row['c_range'],data['program.c']).decode();need(row['symbol']+'(' in text and text.endswith('}\n'),'function definition range')
  s=span(row['source_span'])
  if s is not None:need(s.startswith(('fn '+f['name']+'(').encode()) and s.endswith(b'}'),'source function span')
  role=f['id'] in [v['function'] for v in core['entries'].values()]
  need(text.startswith('_Noreturn void ' if role else 'static '),'role ordinary ABI separation')
  if role:need(not re.search(r'^    return',text,re.M),'no role return')
 for row,p in zip(manifest['primitives'],primitive):
  keys(row,'id operation symbol artifact range');need(row['id']==p['id'] and row['operation']==p['operation'] and row['symbol']=='anl_boot_f'+str(p['id']) and row['artifact']=='c','primitive mapping');need(slice_range(row['range'],data['program.c']).decode()==expected_primitive(p),'exact primitive template')
 instructions={(f['id'],p):ins for f in mir['functions'] if f['kind']=='defined' for p,ins in paths(f['body'])};ordered=[];seen_core=set();ranges={}
 fused={};selected_ranges={}
 keys(manifest['parks'],'boot hardware language')
 for role in ['boot','hardware','language']:
  park=manifest['parks'][role];keys(park,'function core_path mir_path');function=core['entries'][role]['function'];need(park['function']==function,'selected role function')
  selected=selected_tail(core['functions'][function]['body']);need(selected is not None and same(park['core_path'],selected),'independent selected Core occurrence')
  location=path_key(park['mir_path']);parent=(function,location);need(parent in instructions and parent not in selected_ranges,'unique selected MIR occurrence');ins=instructions[parent];op=ins['operation'];need(op['tag']=='while' and ins['destination']['ty']=='unit','selected MIR while type')
  selected_ranges[parent]=park
  for child,field,tag,ty,fragment in [('whileCondition','condition','boolean','bool',b'true'),('whileBody','body','unit','unit',b'(void)0;')]:
   block=op[field];need(len(block['instructions'])==1,'canonical selected singleton block');value=block['instructions'][0]
   need(same(value['destination'],block['yield']) and value['destination']['ty']==ty and value['operation']['tag']==tag,'selected literal yield and type')
   if tag=='boolean':need(value['operation']['value'] is True,'literal true selected condition')
   key=(function,(location[0]+((location[1],child),),0));need(key not in fused and key in instructions,'unique selected child');need(value['destination']['id']!=ins['destination']['id'],'distinct selected parent and child');fused[key]=fragment
  need(op['condition']['yield']['id']!=op['body']['yield']['id'],'distinct selected children')
 for row in manifest['origins']:
  keys(row,'function core_path mir_path source_span c_range');key=(row['function'],path_key(row['mir_path']));need(key in instructions and key not in ordered,'unique structural MIR occurrence');ordered.append(key)
  ck=(row['function'],json.dumps(row['core_path'],sort_keys=True));need(ck not in seen_core,'unique emitting Core occurrence');seen_core.add(ck)
  expr=core_at(core['functions'][row['function']]['body'],row['core_path']);ins=instructions[key];need(expr['ty']==ins['destination']['ty'],'origin type');span(row['source_span']);text=slice_range(row['c_range'],data['program.c']);ranges[key]=row['c_range']
  if key in fused:need(text==fused[key],'exact selected literal C range')
  else:need(('t'+str(ins['destination']['id'])).encode() in text,'actual destination range')
 need(ordered==list(instructions),'complete ordered structural MIR map')
 for parent in selected_ranges:
  function,(blocks,index)=parent;pr=ranges[parent];text=slice_range(pr,data['program.c']);match=re.fullmatch(rb'( *)while \(true\) \{\n\1    \(void\)0;\n\1\}\n\1unsigned char t([0-9]+) = 0;\n',text)
  need(match is not None and int(match.group(2))==instructions[parent]['destination']['id'],'exact selected parent C emission')
  condition=ranges[(function,(blocks+((index,'whileCondition'),),0))];body=ranges[(function,(blocks+((index,'whileBody'),),0))]
  a=pr['start']+text.index(b'true');b=pr['start']+text.index(b'(void)0;');need(condition==dict(start=a,end=a+4) and body==dict(start=b,end=b+8),'exact inline child offsets within selected parent')
 for (f,(blocks,index)),r in ranges.items():
  if blocks:
   parent=(f,(blocks[:-1],blocks[-1][0]));pr=ranges[parent];need(pr['start']<=r['start']<r['end']<=pr['end'],'structured C containment')
 keys(manifest['parks'],'boot hardware language');keys(manifest['abi'],'boot hardware language');assembly='.option norelax\n.option norvc\n'
 for role in ['boot','hardware','language']:
  park=manifest['parks'][role];keys(park,'function core_path mir_path');need(park['function']==core['entries'][role]['function'],'selected role function');need(any(all(same(o[k],park[k]) for k in park) for o in manifest['origins']),'park is actual origin');body=core['functions'][park['function']]['body'];selected=selected_tail(body);need(selected is not None and same(park['core_path'],selected),'exact initializer-first selected park');node=core_at(body,park['core_path']);need(node['tag']=='while' and node['condition']['tag']=='boolean' and node['condition']['value'] is True and node['body']['tag']=='unit','actual source park')
  row=manifest['abi'][role];keys(row,'function stack symbol range');need(same({k:row[k] for k in ['function','stack']},core['entries'][role]),'ABI roles');need(row['symbol']=={'boot':'anl_boot_entry','hardware':'anl_boot_hardware_entry','language':'anl_boot_language_entry'}[role],'ABI symbol');expected=expected_entry(role,row['function']);need(slice_range(row['range'],data['entry.S']).decode()==expected,'exact entry ABI template');assembly+=expected
 assembly+='.section .note.GNU-stack,"",@progbits\n';need(data['entry.S']==assembly.encode(),'exact complete entry assembly')
 need(data['link.ld']==(root/'expected-link.ld').read_bytes(),'exact reviewed linker template')
 for forbidden in ['#include <stdio.h>','#include <stdlib.h>','#include <signal.h>','int main(', 'anl_memory_', 'malloc(', 'exit(', 'apl_trap(', '__builtin_unreachable']:
  need(forbidden not in c,'forbidden hosted/fallback content '+forbidden)
 # Fixed reviewed guard bodies include the closed numerical trap mapping.
 baseline=strict((root/'scalar-helpers.json').read_bytes());need(len(baseline)==25,'reviewed scalar helper inventory');helpers={}
 for m in re.finditer(r'static (?:int64_t|uint64_t) (apl_\w+)\(',c):
  name=m.group(1);actual=function_text(c,m.start());need(name in baseline,'known helper');expected=baseline[name]
  need(actual==expected,'exact guarded scalar helper '+name);helpers[name]=True
 return dict(files={n:dict(bytes=len(v),sha256=sha(v)) for n,v in data.items()},functions=len(defined),primitives=len(primitive),origins=len(ordered),helpers=list(helpers),manifest=manifest)
