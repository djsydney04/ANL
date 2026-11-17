#!/usr/bin/env python3
"""Reproduce frozen ANL flat-product measurements; audit/self-test launch no workloads."""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, pathlib, platform, re, resource, shutil
import signal, statistics, subprocess, sys, time
from datetime import datetime, timezone
HERE = pathlib.Path(__file__).resolve().parent
P = HERE
OUTPUT = None
SOURCES = HERE/'results/flat-products-sources.json'
ARTIFACTS = HERE/'results/flat-products-artifacts.json'
COMPILER_INPUTS = ('src', '.cargo', 'Cargo.toml', 'Cargo.lock', 'build.rs', 'rust-toolchain', 'rust-toolchain.toml')

class GateFailure(RuntimeError): pass

def sha(path): return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
def save(path, value): path.write_text(json.dumps(value, indent=2)+'\n')
def require(test, reason):
    if not test: raise GateFailure(reason)

def validate_result(result, exit_code=0, stdout=None, diagnostic=None):
    require(result['exit']==exit_code, f"exit {result['exit']}, expected {exit_code}")
    if stdout is not None: require(result['stdout']==stdout, 'wrong stdout')
    if exit_code==0: require(not result['stderr'], 'success wrote stderr')
    else: require(bool(result['stderr']), 'failure omitted diagnostic')
    if diagnostic: require(diagnostic in result['stderr'].decode('utf-8',errors='replace'), 'wrong trap/diagnostic')

def identical(a,b,what): require(a==b, f'{what} changed')

def strict_json(data):
    def unique_object(pairs):
        result={}
        for key,value in pairs:
            require(key not in result,'duplicate JSON key: '+key)
            result[key]=value
        return result
    def invalid_constant(value):
        raise GateFailure('non-JSON numeric constant: '+value)
    return json.loads(data,object_pairs_hook=unique_object,parse_constant=invalid_constant)

def json_equal(actual,expected):
    """JSON types are part of the contract: Python bool/int coercion is not."""
    if type(actual) is not type(expected): return False
    if isinstance(expected,dict):
        return actual.keys()==expected.keys() and all(json_equal(actual[k],v) for k,v in expected.items())
    if isinstance(expected,list):
        return len(actual)==len(expected) and all(json_equal(a,e) for a,e in zip(actual,expected))
    return actual==expected

def require_json(data,expected,message):
    require(json_equal(strict_json(data),expected),message)

def validate_artifacts():
    manifest=strict_json(ARTIFACTS.read_text())
    for name,expected in manifest['files'].items():
        path=HERE/name
        require(path.is_file() and not path.is_symlink(),'missing/nonregular benchmark input: '+name)
        require(sha(path)==expected,'benchmark input changed: '+name)
    expected={name for name in manifest['files'] if name.startswith('cases/flat-products/')}
    actual={str(path.relative_to(HERE)) for path in (HERE/'cases/flat-products').rglob('*') if path.is_file()}
    require(actual==expected,'frozen corpus file inventory differs')
    return manifest

def check_checkout(directory,expected,absent):
    """Complete selected checkout inputs, including unexpected build/config files.

    Ancestor/global Cargo configuration and ambient toolchain state are not
    attested by this file inventory. Binary/source binding is a separate claim.
    """
    actual=set()
    def collect(path):
        require(not path.is_symlink(),'symlink compiler input: '+str(path))
        if path.is_dir():
            for child in path.iterdir(): collect(child)
        else:
            require(path.is_file(),'nonregular compiler input: '+str(path))
            actual.add(str(path.relative_to(directory)))
    for name in absent:
        path=directory/name
        require(not path.exists() and not path.is_symlink(),'unexpected compiler/config path: '+name)
    for name in COMPILER_INPUTS:
        path=directory/name
        if path.exists() or path.is_symlink(): collect(path)
    require(actual=={n for n in expected if not n.startswith('tests/')},'compiler input inventory differs')
    for name,digest in expected.items():
        path=directory
        for part in pathlib.Path(name).parts:
            path=path/part
            require(not path.is_symlink(),'symlink source input: '+name)
        require(path.is_file() and sha(path)==digest,'source input differs: '+name)

def validate_package():
    # Called both before and after each run; no builds or implicit repinning.
    validate_artifacts()
    identity=strict_json(SOURCES.read_text());suite=identity['suites'][OPTIONS.suite]
    manifest=strict_json((P/'manifest.json').read_text())
    tools={}
    recorded=strict_json((HERE/'results/flat-products-recorded-tools.json').read_text())
    for side in ('baseline','candidate'):
        role=suite[side];subject=identity['variants'][role]
        source=getattr(OPTIONS,side+'_source')
        require(source is not None,'both source checkouts are required')
        check_checkout(source,subject['files'],identity['checkout_absent_paths'])
        binary=getattr(OPTIONS,side)
        require(binary is not None and binary.is_file(),'supply '+side+' executable')
        supplied=getattr(OPTIONS,side+'_sha256')
        require(not OPTIONS.new_host or supplied is not None,'new-host requires explicit binary hashes')
        expected=supplied if OPTIONS.new_host else subject['binary_sha256']
        require(supplied is None or supplied==expected,'recorded binary identity cannot be replaced without --new-host')
        require(sha(binary)==expected,side+' executable hash differs')
        tools[side]=dict(path=str(binary),sha256=expected,source_role=role,source_files=subject['files'],commit=subject['commit'])
    require(OPTIONS.cc is not None and OPTIONS.cc.is_file(),'supply --cc')
    require(not OPTIONS.new_host or OPTIONS.cc_sha256 is not None,'new-host requires --cc-sha256')
    cc_expected=OPTIONS.cc_sha256 if OPTIONS.new_host else recorded['cc']['sha256']
    require(sha(OPTIONS.cc)==cc_expected,'C compiler identity differs')
    require(OPTIONS.cc_sha256 is None or OPTIONS.cc_sha256==cc_expected,'recorded C compiler identity cannot be replaced without --new-host')
    linker_expected=OPTIONS.linker_sha256 if OPTIONS.new_host else recorded['linker']['sha256']
    require(OPTIONS.linker is not None and OPTIONS.linker.is_file(),'supply --linker')
    require(linker_expected is not None and sha(OPTIONS.linker)==linker_expected,'linker identity differs')
    python_path=pathlib.Path(sys.executable).resolve();python_hash=sha(python_path)
    if not OPTIONS.new_host:
        require(python_hash==recorded['python']['sha256'],'Python identity differs; use --new-host for a new experiment')
        for key,current in [('system',platform.system()),('machine',platform.machine()),('release',platform.release())]:
            require(current==recorded['host'][key],'host differs; use --new-host')
        require(OPTIONS.sdk is not None,'recorded host requires --sdk')
        for name,digest in recorded['sdk_header_sha256'].items():
            require(sha(OPTIONS.sdk/'usr/include'/name)==digest,'SDK header differs: '+name)
        for key,value in recorded['environment'].items():
            actual=os.environ.get(key)
            if value=='<SDK>':
                require(actual is not None and pathlib.Path(actual).resolve()==OPTIONS.sdk,'recorded SDK environment differs')
            else:
                require(actual==value,'recorded environment differs: '+key)
    cc_args=['-isysroot',str(OPTIONS.sdk)] if OPTIONS.sdk else []
    info=dict(baseline_source_revision=tools['baseline']['commit'] or identity['variants'][suite['baseline']].get('source_sha256'),
              baseline_binary=tools['baseline']['path'],baseline_binary_sha256=tools['baseline']['sha256'],
              cc=dict(path=str(OPTIONS.cc),sha256=cc_expected),cc_args=cc_args,
              host=dict(system=platform.system(),machine=platform.machine(),release=platform.release(),logical_cpus=os.cpu_count(),python=platform.python_version()),
              source_identity=tools,python=dict(path=str(python_path),sha256=python_hash),
              linker=dict(path=str(OPTIONS.linker),sha256=linker_expected),
              sdk=dict(path=str(OPTIONS.sdk),headers={name:sha(OPTIONS.sdk/'usr/include'/name) for name in recorded['sdk_header_sha256']}) if OPTIONS.sdk else None,
              identity_mode='new-host' if OPTIONS.new_host else 'recorded-tool-identities',
              source_commit_binding=identity['publication_status'],
              environment={key:os.environ.get(key) for key in ('SDKROOT','CPATH','C_INCLUDE_PATH','LIBRARY_PATH','MACOSX_DEPLOYMENT_TARGET','DYLD_LIBRARY_PATH','DYLD_INSERT_LIBRARIES','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTUP_TOOLCHAIN')})
    require(manifest['samples']==7 and manifest['warmups']==2,'frozen round counts changed')
    return manifest,info

def execute(command, directory, env, timeout, measured=False, cwd=None):
    """Per-child wait4 RSS, never cumulative RUSAGE_CHILDREN maxrss."""
    directory.mkdir(parents=True,exist_ok=False)
    out=directory/'stdout';err=directory/'stderr';expired=False;child=None
    def expire(signum,frame):
        nonlocal expired
        expired=True
        if child is not None:
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
    def output_limit():
        resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024*1024,64*1024*1024))
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    old_handler=signal.signal(signal.SIGALRM,expire)
    try:
        with out.open('wb') as stdout,err.open('wb') as stderr:
            signal.setitimer(signal.ITIMER_REAL,timeout)
            started=time.perf_counter_ns() if measured else None
            child=subprocess.Popen(command,cwd=cwd or P,env=env,stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=output_limit)
            _,status,usage=os.wait4(child.pid,0)
            elapsed=time.perf_counter_ns()-started if measured else None
            child.returncode=os.waitstatus_to_exitcode(status)
    except BaseException:
        if child is not None and child.returncode is None:
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            try:
                _,status,_=os.wait4(child.pid,0)
                child.returncode=os.waitstatus_to_exitcode(status)
            except ChildProcessError: pass
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,old_handler)
    require(not expired,f'timeout after {timeout}s: {command}')
    result=dict(exit=child.returncode,stdout=out.read_bytes(),stderr=err.read_bytes())
    record=dict(command=command,cwd=str(cwd or P),exit=child.returncode,stdout_file=str(out.relative_to(OUTPUT)),stderr_file=str(err.relative_to(OUTPUT)),stdout_sha256=sha(out),stdout_bytes=out.stat().st_size,stderr_sha256=sha(err),stderr_bytes=err.stat().st_size)
    if measured:
        record.update(wall_ns=elapsed,user_cpu_ns=round(usage.ru_utime*1e9),system_cpu_ns=round(usage.ru_stime*1e9),peak_rss_bytes=int(usage.ru_maxrss)*(1 if platform.system()=='Darwin' else 1024))
    return result,record

def command(binary,case,operation,source=None):
    args=[str(binary),operation,str(source or P/case['file'])]
    if operation in ('eval','eval-core'): args += ['--fuel',str(case['fuel'])]
    return args

def gate_operation(result,case,operation):
    expected=b'' if operation=='check' else case['expected'].encode() if operation=='eval' else None
    validate_result(result,stdout=expected)
    if operation=='dump-core':
        artifact=strict_json(result['stdout'])
        require(artifact['schema']==case['core_schema'],'feature core schema changed')
        require(artifact['semantic_revision']==case['semantic_revision'],'feature semantic revision changed')
    if operation=='emit-c':
        require(bool(result['stdout']),'empty C output')
        require(not re.search(rb'\b(?:malloc|calloc|realloc|free)\s*\(',result['stdout']),'emitted C gained allocation calls')

def active_slot_bound(artifact):
    """Conservative logical-slot peak for this acyclic corpus, from typed core.

    Caller cells stay live. A call reserves all arguments before any evaluation;
    the same reservation becomes the callee frame. Let scopes release on return.
    Expression temporaries/tuple scratch are not logical slots in the contract.
    """
    functions=artifact['functions'];memo={};visiting=set()
    def function(index):
        if index in memo: return memo[index]
        require(index not in visiting,'slot-bound corpus must have an acyclic call graph')
        visiting.add(index);bound=expr(functions[index]['body']);visiting.remove(index);memo[index]=bound;return bound
    def expr(e):
        tag=e['tag']
        if tag in ('integer','boolean','unit','local'): return 0
        if tag in ('let','let_mut'): return max(expr(e['value']),1+expr(e['body']))
        if tag in ('assign','project'): return expr(e['value'])
        if tag=='unary': return expr(e['operand'])
        if tag=='tuple': return max((expr(x) for x in e['fields']),default=0)
        if tag=='binary': return max(expr(e['left']),expr(e['right']))
        if tag=='if': return max(expr(e['condition']),expr(e['then']),expr(e['else']))
        if tag=='while': return max(expr(e['condition']),expr(e['body']))
        if tag=='call': return len(e['arguments'])+max(max((expr(x) for x in e['arguments']),default=0),function(e['function']))
        raise GateFailure('unrecognized core constructor in slot analysis: '+tag)
    return function(artifact['entry'])

def retained_core(singleton):
    """Fixed independent core recipe used to justify work counts, not an evaluator."""
    ty={'tuple':['i64']} if singleton else 'i64'
    def integer(n): return dict(tag='integer',ty='i64',value=str(n))
    def local(index,kind='i64'): return dict(tag='local',ty=kind,index=index)
    def binary(op,left,right,kind='i64'): return dict(tag='binary',ty=kind,op=op,left=left,right=right)
    def wrap(e): return dict(tag='tuple',ty=ty,fields=[e]) if singleton else e
    def call(args): return dict(tag='call',ty='i64',function=0,arguments=args)
    def field(index):
        value=local(index,ty)
        return dict(tag='project',ty='i64',index=0,value=value) if singleton else value
    condition=binary('eq',local(256),integer(0),'bool')
    body={'tag':'if','ty':'i64','condition':condition,
          'then':binary('add',field(255),field(0)),
          'else':call([binary('sub',local(256),integer(1))]+[wrap(binary('add',local(256),integer(i))) for i in range(256)])}
    return dict(schema='apl-core-v2' if singleton else 'apl-core-v0',
                semantic_revision='flat-products-2026-11-17' if singleton else 'm1-2026-11-16',entry=1,
                functions=[dict(id=0,name='hold',params=['i64']+[ty]*256,result='i64',body=body),
                           dict(id=1,name='main',params=[],result='i64',body=call([integer(63)]+[wrap(integer(i)) for i in range(256)]))])

def retained_slot_bound(artifact):
    # This bounded corpus has 64 live call-argument frames, each 257 cells.
    # Exact structure must match before applying the closed-form count.
    singleton=artifact.get('schema')=='apl-core-v2'
    require(json_equal(artifact,retained_core(singleton)),'retained-work core recipe changed')
    return 64*257

def summary(samples):
    return {key:dict(median=statistics.median(s[key] for s in samples),minimum=min(s[key] for s in samples),maximum=max(s[key] for s in samples)) for key in ('wall_ns','user_cpu_ns','system_cpu_ns','peak_rss_bytes')}

def self_test():
    good=dict(exit=0,stdout=b'42\n',stderr=b'')
    validate_result(good,stdout=b'42\n')
    mutations=[lambda:validate_result(dict(good,stdout=b'41\n'),stdout=b'42\n'),lambda:validate_result(dict(good,exit=1),stdout=b'42\n'),lambda:validate_result(dict(good,stderr=b'warning\n'),stdout=b'42\n'),lambda:validate_result(dict(exit=2,stdout=b'',stderr=b'wrong_trap'),2,b'','division_by_zero'),lambda:identical(b'original C',b'changed C','C')]
    caught=0
    for mutation in mutations:
        try: mutation()
        except GateFailure: caught+=1
    require(caught==len(mutations),'semantic gate mutation escaped')
    # Independent closed forms, not calls to the compiler or a mirror of its loop.
    require(42+1==43,'pair API oracle inconsistent')
    require(200000*199999//2+3*200000+1==20000500001,'pair checksum oracle inconsistent')
    require(11*100000+6==1100006,'mixed-eight oracle inconsistent')
    require(2*(200000+1)==400002 and 8*(100000+1)==800008,'construction counts inconsistent')
    require(pow(48271,1000000,2147483647)==1263606197,'arithmetic oracle inconsistent')
    require(10000*256-5000==2555000 and 32*(31*32//2)+32==15904,'scalar oracle inconsistent')
    require(1+(1+255)==257 and 64*256==16384 and 64*257==16448,'retained oracle inconsistent')
    require(1+513+64*4+63*1028+5==65539 and 1+257+64*4+63*772+3==49153,'fuel oracle inconsistent')
    return dict(pure_gate_mutations_rejected=caught,external_workloads_invoked=0,timings_recorded=0)

def run(args,manifest,info):
    global OUTPUT
    require(args.output_dir is not None,'supply a fresh --output-dir')
    out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=False);OUTPUT=out
    (out/'tmp').mkdir()
    bins={'baseline':pathlib.Path(info['baseline_binary'])}
    if args.candidate:
        expected=info['source_identity']['candidate']['sha256']
        candidate=args.candidate.resolve()
        require(sha(candidate)==expected,'candidate binary hash mismatch')
        shutil.copy2(candidate,out/'candidate-compiler');bins['candidate']=out/'candidate-compiler'
    require(args.mode!='measure' or 'candidate' in bins,'measure requires a candidate for interleaving')
    env=os.environ.copy();env.update(LANG='C',LC_ALL='C',CC=info['cc']['path'],TMPDIR=str(out/'tmp'))
    report=dict(schema='anl-flat-products-comparison-v1',mode=args.mode,started_utc=datetime.now(timezone.utc).isoformat(),artifact_manifest_sha256=sha(ARTIFACTS),host=info['host'],load_average_start=os.getloadavg(),logical_cpus=os.cpu_count(),binary_sha256={k:sha(v) for k,v in bins.items()},baseline_revision=info['baseline_source_revision'],candidate_source_identity=info['source_identity']['candidate'],experiment_identity=info,candidate_source_binding='Caller must supply separately reviewed release-build provenance; revision text alone is not proof.',semantic_gates=[],native_sizes=[],jobs=[],unexpected_failures=0)
    baseline_outputs={};jobs=[]
    try:
        report['gate_self_test']=self_test()
        for case in manifest['cases']:
            outputs={}
            for side,binary in bins.items():
                outputs[side]={}
                root=out/'gate'/case['name']/side
                for operation in ('check','eval','dump-core','emit-c'):
                    result,record=execute(command(binary,case,operation),root/operation,env,manifest['timeout_seconds'])
                    gate_operation(result,case,operation);outputs[side][operation]=result['stdout']
                    record.update(case=case['name'],side=side,operation=operation);report['semantic_gates'].append(record)
                    if side=='baseline': baseline_outputs[(case['name'],operation)]=result['stdout']
                core_path=root/'dump-core/stdout'
                if 'constructed_fields' in case:
                    counter=retained_slot_bound if args.suite=='retained' else active_slot_bound
                    bound=counter(strict_json(outputs[side]['dump-core']))
                    require(bound<case['active_slots_upper_limit'],'corpus exceeds active-slot budget')
                    require(case['constructed_fields']<case['charged_field_limit'],'corpus exceeds tuple-allocation budget')
                    report.setdefault('work_bounds',[]).append(dict(case=case['name'],side=side,active_slots_upper_bound=bound,constructed_fields=case['constructed_fields'],iterations=case['iterations']))
                result,record=execute(command(binary,case,'eval-core',core_path),root/'eval-core',env,manifest['timeout_seconds'])
                validate_result(result)
                require_json(result['stdout'],dict(outcome='value',type='i64',value=case['expected'].strip()),'core outcome differs from independent expected value')
                record.update(case=case['name'],side=side,operation='eval-core');report['semantic_gates'].append(record)
                for opt in (0,2):
                    native=root/f'native-o{opt}';native.mkdir()
                    (native/'program.c').write_bytes(outputs[side]['emit-c'])
                    cc=[info['cc']['path'],'-std=c11',f'-O{opt}']+info['cc_args']
                    result,record=execute(cc+['-c','program.c','-o','program.o'],native/'compile',env,manifest['timeout_seconds'],cwd=native)
                    validate_result(result,stdout=b'');report['semantic_gates'].append(record)
                    result,record=execute(cc+['program.o','-o','program'],native/'link',env,manifest['timeout_seconds'],cwd=native)
                    validate_result(result,stdout=b'');report['semantic_gates'].append(record)
                    result,record=execute([str(native/'program')],native/'execute',env,manifest['timeout_seconds'])
                    validate_result(result,stdout=case['expected'].encode());report['semantic_gates'].append(record)
                    report['native_sizes'].append(dict(case=case['name'],side=side,optimization=opt,c_bytes=(native/'program.c').stat().st_size,object_bytes=(native/'program.o').stat().st_size,executable_bytes=(native/'program').stat().st_size,object_sha256=sha(native/'program.o'),executable_sha256=sha(native/'program')))
            if 'candidate' in bins:
                for operation in ('dump-core','emit-c'):
                    identical(outputs['baseline'][operation],outputs['candidate'][operation],case['name']+'/'+operation+' bytes')
            for operation in ('check','dump-core','emit-c','eval') if case.get('measure',True) else ():
                jobs.append(dict(ordinal=len(jobs),case=case,operation=operation,samples={k:[] for k in bins},warmups={k:[] for k in bins}))
        for case in manifest['negative_gates']:
            for side,binary in bins.items():
                for operation in ('check','eval'):
                    result,record=execute([str(binary),operation,str(P/case['file'])],out/'negative'/case['name']/side/operation,env,manifest['timeout_seconds'])
                    validate_result(result,case[operation+'_exit'],b'',case.get('trap') if operation=='eval' else None)
                    report['semantic_gates'].append(record)
        for case in manifest['cases']:
            if case.get('low_fuel_gate'):
                for side,binary in bins.items():
                    args_=[str(binary),'eval',str(P/case['file']),'--fuel',str(case['low_fuel_gate'])]
                    result,record=execute(args_,out/'work-gate'/case['name']/side,env,manifest['timeout_seconds'])
                    validate_result(result,3,b'','fuel')
                    record.update(case=case['name'],side=side,operation='bounded-work-witness')
                    report['semantic_gates'].append(record)
                    if case.get('exact_fuel'):
                        exact=[str(binary),'eval',str(P/case['file']),'--fuel',str(case['exact_fuel'])]
                        result,record=execute(exact,out/'exact-work-gate'/case['name']/side,env,manifest['timeout_seconds'])
                        validate_result(result,0,case['expected'].encode())
                        record.update(case=case['name'],side=side,operation='exact-fuel-witness');report['semantic_gates'].append(record)
        for case in manifest['expression_gates']:
            for side,binary in bins.items():
                result,record=execute([str(binary),'eval-core',str(P/case['file'])],out/'typed-outcomes'/case['name']/side,env,manifest['timeout_seconds'])
                validate_result(result)
                require_json(result['stdout'],case['expected'],'wrong typed tuple outcome')
                record.update(case=case['name'],side=side,operation='typed-tuple-outcome')
                report['semantic_gates'].append(record)
        report['native_size_gates']=[]
        size_review=[]
        if 'candidate' in bins:
            for b in [x for x in report['native_sizes'] if x['side']=='baseline']:
                c=next(x for x in report['native_sizes'] if x['side']=='candidate' and x['case']==b['case'] and x['optimization']==b['optimization'])
                grew=[field for field in ('object_bytes','executable_bytes') if c[field]>b[field]]
                if grew: size_review.append(dict(case=b['case'],optimization=b['optimization'],fields=grew))
                report['native_size_gates'].append(dict(case=b['case'],optimization=b['optimization'],status='investigate_size_growth' if grew else 'unchanged_or_smaller'))
        report['semantic_gate_status']='passed'
        if args.mode=='measure':
            report['round_load_average']=[]
            for round_index in range(manifest['warmups']+manifest['samples']):
                report['round_load_average'].append(dict(round=round_index,load=os.getloadavg()))
                for job in jobs if round_index%2==0 else reversed(jobs):
                    order=('baseline','candidate') if (round_index+job['ordinal'])%2==0 else ('candidate','baseline')
                    for side in order:
                        case=job['case'];operation=job['operation'];directory=out/'measure'/f'round-{round_index}'/case['name']/operation/side
                        result,record=execute(command(bins[side],case,operation),directory,env,manifest['timeout_seconds'],measured=True)
                        gate_operation(result,case,operation)
                        identical(result['stdout'],baseline_outputs[(case['name'],operation)],f'{case["name"]}/{operation} output during sample')
                        kind='warmups' if round_index<manifest['warmups'] else 'samples'
                        job[kind][side].append(record)
            review=[str(item) for item in size_review]
            for job in jobs:
                stats={side:summary(samples) for side,samples in job['samples'].items()}
                comparisons={}
                for metric,gate in [('wall_ns',manifest['gates']['wall_median_ratio']),('peak_rss_bytes',manifest['gates']['rss_median_ratio'])]:
                    b=stats['baseline'][metric];c=stats['candidate'][metric];ratio=c['median']/b['median'] if b['median'] else None
                    overlap=not(c['minimum']>b['maximum'] or b['minimum']>c['maximum'])
                    exceeded=ratio is None or (gate is not None and ratio>gate)
                    comparisons[metric]=dict(median_ratio=ratio,threshold=gate,range_overlap=overlap,status='observation_only' if gate is None else 'review_required' if exceeded else 'within_review_threshold')
                    if exceeded: review.append(f"{job['case']['name']}/{job['operation']}/{metric}")
                report['jobs'].append(dict(case=job['case']['name'],operation=job['operation'],warmups=job['warmups'],samples=job['samples'],summary=stats,comparison=comparisons))
            report['performance_verdict']=('review_required' if review else 'within_frozen_review_thresholds') if args.suite.startswith('scalar') else 'measurement_only_no_acceptance_threshold'
            report['performance_policy']=manifest['gates'].get('performance_policy','scalar_investigation_thresholds_not_acceptance')
            report['review_items']=review
            report['performance_limit']='Whole-process observations and investigation thresholds, not release acceptance or proof of no regression. Preserve individual flags and ranges; compare like workloads only. Native throughput and hard memory bounds are not established.'
        _,final_info=validate_package()
        require(json_equal(final_info,info),'source/tool/environment identity changed during run')
        for side,binary in bins.items(): require(sha(binary)==report['binary_sha256'][side],f'{side} binary changed during run')
        report['load_average_end']=os.getloadavg();report['finished_utc']=datetime.now(timezone.utc).isoformat()
        save(out/'report.json',report)
        return out/'report.json'
    except Exception as error:
        report.update(unexpected_failures=1,status='rejected',reason=str(error));save(out/'rejected.json',report);raise

def audit_historical(raw=None,index=None):
    if raw is None:
        with gzip.open(HERE/'results/flat-products-macos-arm64.json.gz','rt') as stream: raw=strict_json(stream.read())
    if index is None: index=strict_json((HERE/'results/flat-products-run-index.json').read_text())
    expected={f'scalar-paired-e0bbf593-0{i}' for i in (1,2)}
    expected|={f'scalar-optimized-db18624e-0{i}' for i in (1,2,3,4)}
    expected|={f'{group}-optimized-db18624e-0{i}' for group in ('tuples','retained') for i in (1,2)}
    require(set(raw['runs'])==expected=={r['id'] for r in index['runs']},'official run inventory changed')
    samples=typed_outcomes=core_exports=0
    source_identity=strict_json(SOURCES.read_text())
    for item in index['runs']:
        archived=raw['runs'][item['id']];report=archived['report']
        encoded=(json.dumps(report,sort_keys=True,separators=(',',':'))+'\n').encode()
        require(hashlib.sha256(encoded).hexdigest()==archived['published_report_sha256']==item['published_report_sha256'],'published report digest differs')
        require(archived['original_report_sha256']==item['original_report_sha256'],'original report identity differs')
        require(report['semantic_gate_status']=='passed' and report['unexpected_failures']==0,'historical semantic failure')
        require(report['performance_verdict']==item['performance_verdict'] and json_equal(report['review_items'],item['review_items']),'historical review flags changed')
        require(len(report['jobs'])==item['timed_jobs'] and len(report['semantic_gates'])==item['semantic_invocations'],'historical record counts changed')
        corpus=source_identity['suites'][archived['suite']]['corpus']
        manifest=strict_json((HERE/'cases/flat-products'/corpus/'manifest.json').read_text())
        cases={case['name']:case for case in manifest['cases']}
        expressions={case['name']:case for case in manifest['expression_gates']}
        for record in report['semantic_gates']:
            operation=record.get('operation')
            if operation not in ('eval-core','typed-tuple-outcome','dump-core'): continue
            value=raw['outputs'][record['stdout_sha256']]['text']
            if operation=='dump-core':
                artifact=strict_json(value)
                case=cases[record['case']]
                require(artifact['schema']==case['core_schema'] and artifact['semantic_revision']==case['semantic_revision'],'historical core schema differs')
                if corpus=='retained': retained_slot_bound(artifact)
                core_exports+=1
            else:
                expected_outcome=(expressions[record['case']]['expected'] if operation=='typed-tuple-outcome' else
                                  dict(outcome='value',type='i64',value=cases[record['case']]['expected'].strip()))
                require_json(value,expected_outcome,'historical typed outcome differs')
                typed_outcomes+=1
        records=list(report['semantic_gates'])
        measured=warmups=0
        for job in report['jobs']:
            for side in ('baseline','candidate'):
                require(len(job['warmups'][side])==2 and len(job['samples'][side])==7,'historical round counts changed')
                require(json_equal(summary(job['samples'][side]),job['summary'][side]),'historical statistics differ from raw observations')
                records.extend(job['warmups'][side]);records.extend(job['samples'][side])
                measured+=len(job['samples'][side]);warmups+=len(job['warmups'][side])
            for metric,comparison in job['comparison'].items():
                baseline=job['summary']['baseline'][metric]['median'];candidate=job['summary']['candidate'][metric]['median']
                ratio=candidate/baseline if baseline else None
                require(ratio==comparison['median_ratio'],'historical ratio differs from observations')
        require(measured==item['sample_invocations'] and warmups==item['warmup_invocations'],'historical sample inventory differs')
        for record in records:
            for stream in ('stdout','stderr'):
                blob=raw['outputs'][record[stream+'_sha256']]
                require(blob['original_sha256']==record[stream+'_sha256'] and blob['original_bytes']==record[stream+'_bytes'],'historical output identity differs')
                published=blob['text'].encode()
                require(len(published)==blob['published_bytes'] and hashlib.sha256(published).hexdigest()==blob['published_sha256'],'published output bytes differ')
        samples+=measured
    text=json.dumps(raw)
    require('/Users/' not in text and 'apl-internal' not in text and '.git/' not in text,'private location escaped publication normalization')
    with gzip.open(HERE/'results/flat-products-measurement-snapshot.json.gz','rt') as stream: snapshot=strict_json(stream.read())
    identities=strict_json(SOURCES.read_text())['variants']
    before=snapshot['variant_evaluator_text']['fixed_payload'];after=snapshot['variant_evaluator_text']['arc_slice']
    for role,text in [('fixed_payload',before),('arc_slice',after)]:
        require(hashlib.sha256(text.encode()).hexdigest()==identities[role]['files']['src/eval.rs'],'variant source digest differs')
    differences={name for name,digest in identities['fixed_payload']['files'].items() if identities['arc_slice']['files'].get(name)!=digest}
    require(differences=={'src/eval.rs'},'variant changes more than the evaluator')
    import difflib
    patch=''.join(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='a/src/eval.rs',tofile='b/src/eval.rs'))
    path=HERE/identities['arc_slice']['patch']
    require(path.read_text()==patch and sha(path)==identities['arc_slice']['patch_sha256'],'variant patch differs from exact evaluator texts')
    return dict(status='all_official_records_valid',runs=len(expected),measured_child_invocations=samples,unique_output_blobs=len(raw['outputs']),strict_typed_outcome_records=typed_outcomes,strict_core_export_records=core_exports,workloads_invoked=0,timings_recorded=0)

def main():
    global OPTIONS,P
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','self-test','validate','gate','measure'))
    parser.add_argument('--suite',choices=('scalar-initial','scalar-optimized','tuples','retained'))
    for side in ('baseline','candidate'):
        parser.add_argument('--'+side,type=pathlib.Path)
        parser.add_argument('--'+side+'-source',type=pathlib.Path)
        parser.add_argument('--'+side+'-sha256')
    parser.add_argument('--cc',type=pathlib.Path)
    parser.add_argument('--cc-sha256')
    parser.add_argument('--linker',type=pathlib.Path)
    parser.add_argument('--linker-sha256')
    parser.add_argument('--sdk',type=pathlib.Path)
    parser.add_argument('--new-host',action='store_true')
    parser.add_argument('--output-dir',type=pathlib.Path)
    OPTIONS=parser.parse_args()
    for name in ('baseline','candidate','baseline_source','candidate_source','cc','linker','sdk','output_dir'):
        value=getattr(OPTIONS,name)
        if value is not None: setattr(OPTIONS,name,value.resolve())
    try:
        if OPTIONS.mode=='audit':
            validate_artifacts();print(json.dumps(audit_historical()));return 0
        if OPTIONS.mode=='self-test':
            validate_artifacts();print(json.dumps(self_test()));return 0
        require(OPTIONS.suite is not None,'supply --suite')
        suite=strict_json(SOURCES.read_text())['suites'][OPTIONS.suite]
        P=HERE/'cases/flat-products'/suite['corpus']
        manifest,info=validate_package()
        if OPTIONS.mode=='validate':print(json.dumps(dict(status='identities_valid',identity=info,workloads_invoked=0,timings_recorded=0)))
        else:print(run(OPTIONS,manifest,info))
        return 0
    except (GateFailure,OSError,ValueError,KeyError,subprocess.SubprocessError) as error:
        print('rejected: '+str(error),file=sys.stderr);return 1
if __name__=='__main__': raise SystemExit(main())
