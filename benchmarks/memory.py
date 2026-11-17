#!/usr/bin/env python3
"""Audit historical evidence; gates and new experiments require explicit tool hashes and fresh output."""
from pathlib import Path
import argparse
import ast
import copy
import gzip
import re
import shlex
import hashlib
import importlib.util
import itertools
import json
import math
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
HERE = BENCH/'cases/memory'
RESULTS = BENCH/'results'
VALIDATION = REPO/'validation/memory'
ACTIVE = None


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1048576), b''):
            digest.update(chunk)
    return digest.hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def invalid(value):
        raise RuntimeError('nonfinite JSON constant')
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_constant=invalid)


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n')


def identity(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'missing or symlinked file: ' + str(path))
    return dict(path=str(path), sha256=sha(path), bytes=path.stat().st_size)


def check_identity(item):
    need(identity(item['path']) == item, 'input/tool bytes changed: ' + item['path'])


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def audit():
    package = read(RESULTS/'memory-artifacts.json')
    for name,item in package['files'].items():
        path=REPO/name
        need(path.is_file() and not path.is_symlink(), 'missing package input: '+name)
        need(sha(path)==item['sha256'] and path.stat().st_size==item['bytes'], 'package input changed: '+name)
    expected={n for n in package['files'] if n.startswith('benchmarks/cases/memory/')}
    actual={str(p.relative_to(REPO)) for p in HERE.rglob('*') if p.is_file()}
    need(expected==actual, 'performance fixture inventory differs')
    manifest=read(HERE/'manifest.json')
    need(len(manifest['rows'])==6 and len(manifest['schedule'])==336 and manifest['warmup_rounds']==2 and manifest['sample_rounds']==6, 'fixed schedule shape differs')
    for row in manifest['rows']:
        if row['group']=='control':
            need(sha(HERE/row['source'])==row['original']['sha256'], 'unchanged control bytes differ')
    if ACTIVE is None:
        return manifest, None
    inventory=ACTIVE
    for item in list(inventory['tools'].values())+inventory['files']:
        check_identity(item)
    manifest['ordinary_environment']=inventory['environment']
    return manifest, inventory


def helpers():
    oracle=load('oracle',VALIDATION/'oracle.py')
    protocol=load('memory_reference_protocol',VALIDATION/'reference_protocol.py')
    return oracle,protocol


def ordinary_environment(manifest, environment):
    need(environment == manifest['ordinary_environment'], 'measurement environment differs or includes instrumentation')
    need(not any('TRACE' in k or 'REPLAY' in k or k.startswith('ANL_CORPUS_') for k in environment),
         'instrumented ordinary environment')


def execute(argv, directory, environment, phase, timeout):
    """Adapted from the existing product benchmark's wait4 capture; gates are untimed."""
    directory.mkdir(parents=True, exist_ok=False)
    out, err = directory/'stdout', directory/'stderr'
    command = [str(a) for a in argv]
    measured = phase in ('warmup','sample')
    record = dict(argv=command,cwd=str(REPO),environment=environment,phase=phase,
                  timeout_seconds=timeout,complete=False,exit=None,timeout=False,
                  wall_ns=None,user_cpu_ns=None,system_cpu_ns=None,peak_rss_bytes=None)
    save(directory/'command.json',record)
    child = None
    expired = False
    def expire(signum,frame):
        nonlocal expired
        expired = True
        if child is not None:
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
    def bounds():
        resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024*1024,64*1024*1024))
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    old = signal.signal(signal.SIGALRM,expire)
    try:
        with out.open('wb') as stdout, err.open('wb') as stderr:
            signal.setitimer(signal.ITIMER_REAL,timeout)
            started = time.perf_counter_ns() if measured else None
            child = subprocess.Popen(command,cwd=REPO,env=environment,stdin=subprocess.DEVNULL,
                stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=bounds)
            if expired:
                os.killpg(child.pid,signal.SIGKILL)
            _,status,usage = os.wait4(child.pid,0)
            wall = time.perf_counter_ns()-started if measured else None
            child.returncode = os.waitstatus_to_exitcode(status)
        record.update(complete=True,exit=child.returncode,timeout=expired)
        if measured:
            record.update(wall_ns=wall,user_cpu_ns=round(usage.ru_utime*1e9),
                system_cpu_ns=round(usage.ru_stime*1e9),peak_rss_bytes=int(usage.ru_maxrss)*(1 if platform.system()=='Darwin' else 1024),
                wait4_raw={key:getattr(usage,key) for key in dir(usage) if key.startswith('ru_')},
                rss_semantics='wait4 reaped immediate-child maximum; never summed simultaneous process-tree RSS',
                rss_native_unit='bytes' if platform.system()=='Darwin' else 'KiB')
    except BaseException as error:
        record['capture_error'] = str(error)
        if child is not None and child.returncode is None:
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            try:
                _,status,_ = os.wait4(child.pid,0)
                record['exit'] = child.returncode = os.waitstatus_to_exitcode(status)
            except ChildProcessError: pass
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,old)
        for name,path in [('stdout',out),('stderr',err)]:
            if path.exists():
                record[name+'_sha256'] = sha(path)
                record[name+'_bytes'] = path.stat().st_size
        record['timeout'] = expired
        save(directory/'command.json',record)
    need(not expired, 'timeout; complete partial evidence retained at ' + str(directory))
    need(record['stdout_bytes'] <= 64*1024*1024 and record['stderr_bytes'] <= 65536, 'capture bound exceeded')
    return dict(exit=record['exit'],stdout=out.read_bytes(),stderr=err.read_bytes()),record


def outcome(result, expected):
    need(type(result['exit']) is int and result['exit'] == expected['exit'], 'wrong exit/status or trap')
    need(result['stdout'] == expected['stdout'].encode(), 'wrong or missing completed value')
    need(result['stderr'] == expected['stderr'].encode(), 'unexpected diagnostic')


def metric_record(record, command, phase, environment):
    need(record.get('complete') is True and record.get('timeout') is False and type(record.get('exit')) is int,
         'missing/invalid measurement completion')
    need(record['exit'] == 0 and record['argv'] == [str(a) for a in command] and record['phase'] == phase,
         'measurement command/status/phase differs')
    need(record['environment'] == environment, 'mixed instrumentation/environment')
    for key in ('wall_ns','user_cpu_ns','system_cpu_ns','peak_rss_bytes'):
        need(type(record.get(key)) is int and record[key] >= (1 if key in ('wall_ns','peak_rss_bytes') else 0),
             'missing/invalid measurement: ' + key)
    for key in ('stdout','stderr'):
        need(type(record.get(key+'_bytes')) is int and record[key+'_bytes'] >= 0 and
             type(record.get(key+'_sha256')) is str and len(record[key+'_sha256']) == 64, 'missing raw capture identity')


def native_binding(records, expected, memory):
    need(records and all(r['exit'] == 0 and r['changed_arguments'] is False for r in records), 'missing native binding/capture')
    found = set()
    for item in records:
        need(not any('ANL_MEMORY_EVIDENCE' in a or a.startswith('-flto') for a in item['argv']), 'mixed native instrumentation/LTO')
        for source in item['inputs']:
            name = Path(source['path']).name
            need(name != 'evidence.h', 'instrumented header in native binding')
            if name in expected:
                need(source['sha256'] == expected[name], 'actual compiled bytes differ: ' + name)
                found.add(name)
    need(found == set(expected), 'missing actual native input binding')
    if memory:
        compiles = [r for r in records if '-c' in r['argv']]
        need(len(compiles) == 2 and all('-fno-lto' in r['argv'] for r in records), 'not separate production compilation')
        need(len(records) == 3, 'unexpected native command count')
        need(all(r['argv'][1:7] == ['-std=c11','-O2','-fno-lto','-x','c','-c'] for r in compiles),
             'native compile flags differ from production')
        need({Path(r['argv'][7]).name for r in compiles} == {'program.c','runtime.c'}, 'missing separate program/runtime compilation')
    else:
        need(len(records)==1 and records[0]['argv'][1:5]==['-std=c11','-O2','-x','c'], 'scalar production compile flags differ')


def validate_schedule(records, schedule):
    need(type(records) is list and len(records) == len(schedule), 'missing measurement records')
    for record, job in zip(records, schedule):
        need(record.get('job') == job, 'measurement schedule differs')


def offline_discriminators(manifest):
    rejected = []
    def reject(label, action):
        try: action()
        except (RuntimeError,KeyError,TypeError,ValueError): rejected.append(label)
        else: raise RuntimeError('corruption accepted: ' + label)
    expected = dict(exit=0,stdout='42\n',stderr='')
    good = dict(exit=0,stdout=b'42\n',stderr=b'')
    outcome(good,expected)
    reject('wrong_value',lambda:outcome(dict(good,stdout=b'43\n'),expected))
    reject('wrong_status_or_trap',lambda:outcome(dict(good,exit=2,stderr=b'arithmetic_overflow'),expected))
    pinned = identity(HERE/'inputs/constant.anl')
    reject('changed_input',lambda:check_identity(dict(pinned,sha256='0'*64)))
    pinned = identity(BENCH/'memory.py')
    reject('changed_tool',lambda:check_identity(dict(pinned,sha256='0'*64)))
    expected_native={'program.c':'a'*64,'runtime.c':'b'*64,'runtime.h':'c'*64}
    records=[dict(exit=0,changed_arguments=False,argv=['cc','-std=c11','-O2','-fno-lto','-x','c','-c','program.c'],inputs=[dict(path=n,sha256=h) for n,h in expected_native.items()]),
             dict(exit=0,changed_arguments=False,argv=['cc','-std=c11','-O2','-fno-lto','-x','c','-c','runtime.c'],inputs=[]),
             dict(exit=0,changed_arguments=False,argv=['cc','-fno-lto'],inputs=[])]
    native_binding(records,expected_native,True)
    reject('missing_native_binding',lambda:native_binding([],expected_native,True))
    bad=copy.deepcopy(records);bad[0]['inputs'].pop()
    reject('missing_runtime_header',lambda:native_binding(bad,expected_native,True))
    bad=copy.deepcopy(records);bad[0]['argv'].append('-DANL_MEMORY_EVIDENCE=1')
    reject('mixed_native_instrumentation',lambda:native_binding(bad,expected_native,True))
    env=manifest['ordinary_environment']
    ordinary_environment(manifest,env)
    reject('mixed_environment_instrumentation',lambda:ordinary_environment(manifest,dict(env,ANL_MEMORY_TRACE='capture')))
    command=['program']
    good_record=dict(complete=True,timeout=False,exit=0,argv=command,phase='sample',environment=env,
        wall_ns=1,user_cpu_ns=0,system_cpu_ns=0,peak_rss_bytes=1,stdout_bytes=3,stderr_bytes=0,
        stdout_sha256='a'*64,stderr_sha256='b'*64)
    metric_record(good_record,command,'sample',env)
    for key,value in [('wall_ns',None),('wall_ns',0),('user_cpu_ns',-1),('peak_rss_bytes',float('nan')),
                      ('complete',False),('timeout',True),('exit',True),('phase','gate')]:
        reject('invalid_measurement_'+key+'_'+str(value),lambda key=key,value=value:
               metric_record(dict(good_record,**{key:value}),command,'sample',env))
    bad=dict(good_record);del bad['system_cpu_ns']
    reject('missing_measurement_record',lambda:metric_record(bad,command,'sample',env))
    job=dict(phase='sample',round=0,case='constant',operation='native',side='candidate')
    scheduled=dict(good_record,job=job)
    validate_schedule([scheduled],[job])
    reject('missing_scheduled_sample',lambda:validate_schedule([],[job]))
    reject('changed_sample_order',lambda:validate_schedule([dict(scheduled,job=dict(job,round=1))],[job]))
    return dict(status='PASS',rejected=rejected,compiler_executions=0,workload_executions=0,timings_collected=False)


class Experiment:
    def __init__(self, manifest, inventory, root):
        self.m,self.i,self.root = manifest,inventory,root
        self.env = manifest['ordinary_environment']
        ordinary_environment(manifest,self.env)
        self.tools = {name:Path(item['path']) for name,item in inventory['tools'].items()}
        self.O,self.reference = helpers()
        self.native = {}
        self.records = []
        self.counter = 0
        self.capture_launcher = self.root/'cc-adapter-launcher'
        self.capture_launcher.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(VALIDATION/'cc_adapter.py'))+' "$@"\n')
        self.capture_launcher.chmod(0o700)

    def call(self,label,argv,phase='gate',timeout=45,environment=None,expected=None):
        environment = self.env if environment is None else environment
        if phase in ('warmup','sample'):
            ordinary_environment(self.m,environment)
        self.counter += 1
        directory = self.root/'commands'/f'{self.counter:04d}-{phase}-{label}'
        result,record = execute(argv,directory,environment,phase,timeout)
        if expected is not None:outcome(result,expected)
        if phase in ('warmup','sample'):metric_record(record,argv,phase,self.env)
        record['capture_directory'] = str(directory)
        self.records.append(record)
        return result,record

    def quiet(self,label,argv,**kwargs):
        return self.call(label,argv,expected=dict(exit=0,stdout='',stderr=''),**kwargs)

    def bundle(self,row,source,label):
        bundle = self.root/'bundles'/label
        bundle.parent.mkdir(exist_ok=True)
        self.quiet('export-'+label,[self.tools['exporter'],source,bundle],timeout=row['timeouts']['export'])
        manifest = self.O.strict((bundle/'manifest.json').read_bytes())
        self.O.keys(manifest,('schema','semantic_revision','runtime','allocation_profile','compiler','files','sources'))
        need(manifest['schema']=='anl-memory-evidence-bundle-v1' and manifest['runtime']=='default', 'bundle runtime/schema')
        need(manifest['semantic_revision']==self.O.REVISION and self.O.same(manifest['allocation_profile'],self.m['profile']), 'bundle semantics/profile')
        need(manifest['compiler']==dict(version='0.1.0',sha256=self.i['tools']['exporter']['sha256'],memory_evidence=True), 'bundle tool identity')
        files={n:dict(sha256=sha(bundle/n),bytes=(bundle/n).stat().st_size) for n in ('core.json','mir.json','program.c','runtime.c','runtime.h')}
        need(manifest['files']==files,'bundle file inventory')
        need(manifest['sources']==[dict(path_bytes_hex=os.fsencode(source).hex(),sha256=sha(source),bytes=source.stat().st_size)], 'bundle source graph')
        dumped,_=self.call('dump-core-'+label,[self.tools['candidate'],'dump-core',source])
        need(dumped['exit']==0 and dumped['stderr']==b'' and dumped['stdout']==(bundle/'core.json').read_bytes(), 'default/exported Core differs')
        emitted,_=self.call('emit-c-'+label,[self.tools['candidate'],'emit-c',source])
        need(emitted['exit']==0 and emitted['stderr']==b'' and emitted['stdout']==(bundle/'program.c').read_bytes(), 'default/exported C differs')
        pair,_=self.call('pair-'+label,[self.tools['pair'],bundle/'core.json',bundle/'mir.json'],timeout=row['timeouts']['pair'])
        need(pair['stderr']==b'', 'pair diagnostic')
        self.O.assert_pair_report(pair,'accepted',self.m['profile'])
        need(files=={n:dict(sha256=sha(bundle/n),bytes=(bundle/n).stat().st_size) for n in files}, 'bundle changed during gate')
        return bundle

    def capture_build(self,row,side,expected):
        label=row['name']+'-'+side
        capture=self.root/'cc'/label
        binary=self.root/'native'/label/'program'
        binary.parent.mkdir(parents=True)
        environment=dict(self.env,CC=str(self.capture_launcher),ANL_CORPUS_SCRATCH=str(self.root),
            ANL_CORPUS_REAL_CC=str(self.tools['cc']),ANL_CORPUS_REAL_CC_SHA256=self.i['tools']['cc']['sha256'],
            ANL_CORPUS_CC_LOG=str(capture))
        self.quiet('build-'+label,[self.tools[side],'build',HERE/row['source'],'-o',binary],
                   environment=environment,phase='first',timeout=row['timeouts']['build'])
        records=[]
        for path in sorted(capture.glob('call-*/command.json')):
            record=read(path)
            need(record['real_cc_sha256']==self.i['tools']['cc']['sha256'] and record['argv'][0]==str(self.tools['cc']), 'CC identity')
            for item in record['inputs']:
                need(sha(path.parent/item['file'])==item['sha256'] and (path.parent/item['file']).stat().st_size==item['bytes'], 'captured C input changed')
            records.append(record)
        native_binding(records,expected,row['group']=='buffer')
        item=identity(binary)
        self.native[(row['name'],side)]=item
        save(binary.parent/'BINDING.json',dict(native=item,actual_inputs=expected,captures=str(capture),runtime='default',instrumentation=False))
        self.call('native-'+label,[binary],phase='first',timeout=row['timeouts']['native'],expected=row['expected'])

    def c_build(self,row):
        directory=self.root/'native'/(row['name']+'-c')
        directory.mkdir(parents=True)
        cc=self.tools['cc']
        source=HERE/row['c_source']
        flags=self.m['c_flags']
        objects=[]
        for path in ([source,HERE/'c/buffer.c'] if row['group']=='buffer' else [source]):
            obj=directory/(path.stem+'.o')
            self.quiet('c-compile-'+row['name']+'-'+path.stem,[cc,*flags,'-x','c','-c',path,'-o',obj],timeout=120)
            objects.append(obj)
        binary=directory/'program'
        self.quiet('c-link-'+row['name'],[cc,'-fno-lto',*objects,'-o',binary],timeout=120)
        self.native[(row['name'],'c')]=identity(binary)
        save(directory/'BINDING.json',dict(native=identity(binary),sources=[identity(source),identity(HERE/'c/common.h')]+
            ([identity(HERE/'c/buffer.h'),identity(HERE/'c/buffer.c')] if row['group']=='buffer' else []),
            objects=[identity(p) for p in objects],compiler=self.i['tools']['cc'],instrumentation=False))
        self.call('native-'+row['name']+'-c',[binary],phase='first',timeout=row['timeouts']['native'],expected=row['expected'])

    def preflight(self):
        for row in self.m['rows']:
            source=HERE/row['source']
            outputs={}
            for side in row['compiler_sides']:
                self.quiet('check-'+row['name']+'-'+side,[self.tools[side],'check',source],phase='first',timeout=row['timeouts']['check'])
                self.call('eval-'+row['name']+'-'+side,[self.tools[side],'eval',source,'--fuel',row['fuel']],
                          phase='first',timeout=row['timeouts']['eval'],expected=row['expected'])
                if row['group']=='control':
                    outputs[side]={}
                    for op in ('dump-core','emit-c'):
                        result,_=self.call(op+'-'+row['name']+'-'+side,[self.tools[side],op,source])
                        need(result['exit']==0 and result['stderr']==b'', 'control export failed')
                        outputs[side][op]=result['stdout']
            if row['group']=='control':
                need(outputs['baseline']==outputs['candidate'], 'unchanged control Core/C bytes differ')
                # Legacy scalar emit-c adds one CLI newline beyond the translation unit.
                c=outputs['candidate']['emit-c']
                if row['name'] != 'tuple-calls':
                    need(c.endswith(b'\n'),'scalar emit terminator');c=c[:-1]
                expected={'program.c':hashlib.sha256(c).hexdigest()}
            else:
                bundle=self.bundle(row,source,row['name'])
                expected={name:sha(bundle/name) for name in ('program.c','runtime.c','runtime.h')}
                result,_=self.call('eval-core-'+row['name'],[self.tools['candidate'],'eval-core',bundle/'core.json','--fuel',row['fuel']],timeout=row['timeouts']['eval'])
                self.O.assert_execution(result,dict(outcome='value',type='i64',value=row['expected']['stdout'].strip()),wire=True)
                need(result['stderr']==b'', 'eval-core diagnostic')
                companion=row['companion']
                cb=self.bundle(row,HERE/companion['source'],row['name']+'-companion')
                result,_=self.call('reference-'+row['name'],[self.tools['reference'],cb/'core.json',HERE/'response-plan.json',
                    companion['fuel'],companion['transitions']],timeout=row['timeouts']['reference'])
                core=self.O.strict((cb/'core.json').read_bytes())
                report=self.reference.protocol(result,dict(status='value',fuel=companion['fuel'],transitions=companion['transitions'],profile=self.m['profile']),self.O.heap_sites(core))
                need(report['status']=='value' and report['trace']['completion']==dict(kind='value',type='i64',value=companion['value']),
                     'companion incomplete or wrong independent value')
                events=report['trace']['events']
                pairs=4 if row['name']=='buffer-owners' else 1
                length=16 if row['name']=='buffer-owners' else 8
                sites=self.O.heap_sites(core)
                need(len(sites)==1,'unexpected companion sites')
                function,heap=next(iter(sites))
                expected_events=[]
                for index in range(pairs):
                    site=dict(function=function,heap=heap)
                    expected_events += [dict(kind='request',request=str(index),site=site,length=str(length),response='success'),
                                        dict(kind='release',request=str(index),site=site)]
                need(events==expected_events,'companion request/release trace differs')
                self.call('companion-eval-'+row['name'],[self.tools['candidate'],'eval',HERE/companion['source'],'--fuel',companion['fuel']],
                    timeout=45,expected=dict(exit=0,stdout=companion['value']+'\n',stderr=''))
            for side in row['compiler_sides']:self.capture_build(row,side,expected)
            self.c_build(row)
        audit()
        save(self.root/'PREFLIGHT.json',dict(status='PASS',timings_collected=False,native_bindings=list(self.native.values()),
            pair_gate='actual exported measured and companion buffer Core/MIR only',
            reference_gate='small companions only; measured inputs keep independent mathematical oracles'))

    def context(self,label):
        save(self.root/('HOST-'+label+'.json'),dict(platform=platform.platform(),machine=platform.machine(),
            logical_cpus=os.cpu_count(),load_average=os.getloadavg(),environment=self.env))
        for key,argv in [('processes',[self.tools['ps'],'-axo','pid,ppid,pcpu,pmem,comm']),
                         ('power',[self.tools['pmset'],'-g','batt']),('thermal',[self.tools['pmset'],'-g','therm'])]:
            result,_=self.call('host-'+label+'-'+key,argv,phase='context',timeout=10)
            need(result['exit']==0, 'host context query failed: '+label+'/'+key)

    def measure(self):
        rows={r['name']:r for r in self.m['rows']}
        records=[]
        for number,job in enumerate(self.m['schedule']):
            row=rows[job['case']];side=job['side'];op=job['operation'];phase=job['phase']
            source=HERE/row['source']
            check_identity(self.i['tools']['cc'])
            need(sha(source)==read(HERE/'FREEZE.json')['files'][row['source']]['sha256'],'measured source changed')
            if side!='c':check_identity(self.i['tools'][side])
            if op=='native':
                native=self.native[(row['name'],side)]
                check_identity(native)
                argv=[native['path']]
                expected=row['expected']
            else:
                argv=[self.tools[side],op,source]
                expected=row['expected'] if op=='eval' else dict(exit=0,stdout='',stderr='')
                if op=='eval':argv += ['--fuel',row['fuel']]
                if op=='build':
                    binary=self.root/'builds'/f'{number:04d}-{row["name"]}-{side}'/'program'
                    binary.parent.mkdir(parents=True)
                    argv += ['-o',binary]
            _,record=self.call(f'{number:04d}-{row["name"]}-{side}-{op}',argv,phase=phase,timeout=row['timeouts'][op],expected=expected)
            if op=='build':
                generated=identity(binary)
                pinned=self.native[(row['name'],side)]
                need(generated['sha256']==pinned['sha256'] and generated['bytes']==pinned['bytes'], 'ordinary build differs from bound default native artifact')
                record['native_artifact']=generated
                # Outcome gate is outside the timed build interval and outside sample summaries.
                self.call('post-build-'+str(number),[binary],phase='gate',timeout=row['timeouts']['native'],expected=row['expected'])
            elif op=='native':record['native_artifact']=native
            record.update(job=job)
            records.append(record)
            save(self.root/'MEASUREMENTS.json',dict(status='IN_PROGRESS',records=records))
        audit()
        for native in self.native.values():check_identity(native)
        validate_schedule(records,self.m['schedule'])
        summaries={}
        for row in self.m['rows']:
            for op in ('check','eval','build','native'):
                for side in row['native_sides'] if op=='native' else row['compiler_sides']:
                    selected=[r for r in records if r['job']==dict(phase='sample',round=r['job']['round'],case=row['name'],operation=op,side=side)]
                    need(len(selected)==self.m['sample_rounds'],'missing sample records')
                    key='/'.join((row['name'],op,side))
                    summaries[key]={metric:dict(median=statistics.median(r[metric] for r in selected),
                        minimum=min(r[metric] for r in selected),maximum=max(r[metric] for r in selected))
                        for metric in ('wall_ns','user_cpu_ns','system_cpu_ns','peak_rss_bytes')}
                    summaries[key]['samples']=len(selected)
        save(self.root/'MEASUREMENTS.json',dict(status='COMPLETE',records=records,summaries=summaries,
             verdict='Observations only. Limiter, variance, and pipeline differences need independent review; no automatic speedup claim.'))


def source_inputs(root, files):
    root=root.resolve(strict=True)
    items=[]
    for name,expected in files.items():
        actual=identity(root/name)
        need(actual['sha256']==expected['sha256'] and actual['bytes']==expected['bytes'], 'compiler source differs: '+name)
        items.append(actual)
    for directory in ('src','runtime','.cargo'):
        path=root/directory
        if path.exists():
            actual={str(p.relative_to(root)) for p in path.rglob('*') if p.is_file()}
            need(actual=={n for n in files if n.startswith(directory+'/')}, 'compiler input set differs: '+directory)
    for name in ('build.rs','Cargo.toml','Cargo.lock','rust-toolchain','rust-toolchain.toml'):
        need((root/name).exists()==(name in files), 'compiler configuration differs: '+name)
    return items


def configure(args):
    global ACTIVE
    bindings=read(RESULTS/'memory-sources.json')
    tool_inputs={}
    for name in ('baseline','candidate','exporter','pair','reference','cc','linker'):
        path=getattr(args,name).resolve(strict=True)
        item=identity(path)
        need(os.access(path,os.X_OK),'nonexecutable tool: '+name)
        need(re.fullmatch('[0-9a-f]{64}',getattr(args,name+'_sha256')) is not None and item['sha256']==getattr(args,name+'_sha256'),'explicit tool hash differs: '+name)
        tool_inputs[name]=item
    need(Path(tool_inputs['linker']['path'])==(Path(tool_inputs['cc']['path']).parent/'ld').resolve(), 'selected linker must be the compiler-directory ld')
    need(platform.system()=='Darwin','this controller requires Darwin host-context commands; other hosts need a separately reviewed context adaptation')
    for name,path in [('python',Path(sys.executable).resolve()),('ps',args.ps.resolve()),('pmset',args.pmset.resolve())]:
        tool_inputs[name]=identity(path)
    files=[]
    for side in ('baseline','candidate'):
        files += source_inputs(getattr(args,side+'_source'),bindings[side]['files'])
    sdk=args.sdk.resolve(strict=True)
    files += [identity((sdk/'SDKSettings.json').resolve(strict=True)),identity((sdk/'usr/lib/libSystem.tbd').resolve(strict=True))]
    for name in read(RESULTS/'memory-artifacts.json')['files']:
        files.append(identity(REPO/name))
    environment=dict(CC=tool_inputs['cc']['path'],PATH=str(Path(tool_inputs['cc']['path']).parent)+':/usr/bin:/bin',LANG='C',LC_ALL='C',SDKROOT=str(sdk))
    ACTIVE=dict(schema='anl-owned-buffer-performance-new-experiment-inputs-v1',tools=tool_inputs,files=files,environment=environment,
        experiment_kind='new experiment; original measurement identities remain historical',
        source_bindings_sha256=sha(RESULTS/'memory-sources.json'),package_sha256=sha(RESULTS/'memory-artifacts.json'))
    return audit()


def archive_audit():
    archive=read_gzip(RESULTS/'memory-macos-arm64-evidence.json.gz')
    need(archive['schema']=='anl-owned-buffer-public-evidence-v1','historical evidence schema')
    entries={e['id']:e for e in archive['entries']}
    need(len(entries)==len(archive['entries']),'duplicate historical entry')
    for entry in entries.values():
        if entry['disposition']=='text':
            data=entry['text'].encode()
            need(len(data)==entry['normalized_bytes'] and hashlib.sha256(data).hexdigest()==entry['normalized_sha256'],'normalized archive bytes differ')
        else:need(entry['disposition']=='identity-only' and entry['original_bytes']>0,'invalid omitted payload')
    def parsed(name):return json.loads(entries[name]['text'])
    measured=parsed('v3-run/MEASUREMENTS.json')
    manifest=read(HERE/'manifest.json')
    need([r['job'] for r in measured['records']]==manifest['schedule'],'archived schedule differs')
    historical=parsed('v3-preparation/manifest.json')
    need(len(measured['records'])==336 and len({r['capture_directory'] for r in measured['records']})==336,'distinct archived measurements')
    need(sum(r['phase']=='warmup' for r in measured['records'])==84 and sum(r['phase']=='sample' for r in measured['records'])==252,'archived phase counts')
    for record in measured['records']:
        metric_record(record,record['argv'],record['job']['phase'],historical['ordinary_environment'])
        ordinary_environment(historical,record['environment'])
        name=record['capture_directory'].replace('@EXPERIMENT_V3/','v3-run/')+'/command.json'
        need(name in entries,'archived measurement capture missing')
        raw=parsed(name)
        need({k:v for k,v in record.items() if k not in ('job','native_artifact','capture_directory')}==raw,'archived measurement differs from capture')
        usage=raw['wait4_raw']
        need(all(type(v) in (int,float) and math.isfinite(v) and v>=0 for v in usage.values()),'nonfinite/negative archived wait4')
        need(raw['rss_native_unit']=='bytes' and raw['peak_rss_bytes']==usage['ru_maxrss'],'archived RSS unit')
        need(raw['user_cpu_ns']==round(usage['ru_utime']*1e9) and raw['system_cpu_ns']==round(usage['ru_stime']*1e9),'archived CPU units')
    summaries={}
    for row in manifest['rows']:
        for op in ('check','eval','build','native'):
            for side in row['native_sides'] if op=='native' else row['compiler_sides']:
                selected=[r for r in measured['records'] if r['job']['phase']=='sample' and r['job']['case']==row['name'] and r['job']['operation']==op and r['job']['side']==side]
                need(len(selected)==6,'archived sample missing')
                key='/'.join((row['name'],op,side))
                summaries[key]={metric:dict(median=statistics.median(r[metric] for r in selected),minimum=min(r[metric] for r in selected),maximum=max(r[metric] for r in selected)) for metric in ('wall_ns','user_cpu_ns','system_cpu_ns','peak_rss_bytes')}
                summaries[key]['samples']=6
    need(summaries==measured['summaries']==read(RESULTS/'memory-macos-arm64-summary.json')['summaries'],'historical summaries differ')
    for prefix,count in [('v3-run',519),('v2-failed-run',49)]:
        names=sorted(n for n in entries if n.startswith(prefix+'/commands/') and n.endswith('/command.json'))
        need(len(names)==count,'archived command count')
        for index,name in enumerate(names):
            record=parsed(name)
            need(record['complete'] is True and record['timeout'] is False,'incomplete historical command')
            need(record['exit']==(1 if prefix=='v2-failed-run' and index==48 else 0),'historical status differs')
            for stream in ('stdout','stderr'):
                raw=entries[name.rsplit('/',1)[0]+'/'+stream]
                need(record[stream+'_bytes']==raw['original_bytes'] and record[stream+'_sha256']==raw['original_sha256'],'original raw capture identity differs')
    need(parsed('v3-syntax-qualification/RESULT.json')['status']=='PASS','historical syntax qualification')
    return dict(status='PASS',historical_commands=568,historical_measurements=336,historical_samples=252,series=42,project_executions=0)


def read_gzip(path):
    return json.loads(gzip.decompress(Path(path).read_bytes()))


def main():
    parser=argparse.ArgumentParser(description='Audit recorded owned-buffer observations, run untimed gates, or run one fresh fixed experiment.')
    sub=parser.add_subparsers(dest='mode',required=True)
    sub.add_parser('audit',help='read-only fixture/archive checks and offline fault rejection; launches no tools')
    for mode in ('gate','experiment'):
        command=sub.add_parser(mode)
        for name in ('baseline','candidate','exporter','pair','reference','cc','linker'):
            command.add_argument('--'+name,type=Path,required=True)
            command.add_argument('--'+name+'-sha256',required=True)
        for name in ('baseline-source','candidate-source','sdk','output-dir'):
            command.add_argument('--'+name,type=Path,required=True)
        command.add_argument('--ps',type=Path,default=Path('/bin/ps'))
        command.add_argument('--pmset',type=Path,default=Path('/usr/bin/pmset'))
    args=parser.parse_args()
    manifest,_=audit()
    if args.mode=='audit':
        # The offline validator needs an explicit environment but never starts a process.
        manifest['ordinary_environment']={'CC':'offline','PATH':'offline','LANG':'C','LC_ALL':'C','SDKROOT':'offline'}
        print(json.dumps(dict(archive=archive_audit(),fault_rejection=offline_discriminators(manifest)),indent=2))
        return
    manifest,inventory=configure(args)
    offline_discriminators(manifest)
    root=args.output_dir.resolve()
    need(root!=REPO and root!=HERE and not root.exists(),'choose a fresh output directory')
    root.mkdir(parents=True,exist_ok=False)
    save(root/'IDENTITY.json',dict(inventory=inventory,mode=args.mode,package_sha256=sha(RESULTS/'memory-artifacts.json'),new_experiment=True))
    experiment=None
    try:
        experiment=Experiment(manifest,inventory,root)
        experiment.context('before')
        experiment.preflight()
        if args.mode=='experiment':
            experiment.context('pre-samples')
            experiment.measure()
        experiment.context('after')
        audit()
        save(root/'RESULT.json',dict(status='COMPLETE',mode=args.mode,experiment_kind='new experiment',unexpected_failures=0,retries=0,sample_exclusions=0,cache_flushes=0,profiling=False,timings_collected=args.mode=='experiment',interpretation='observations only; independent review required'))
    except BaseException as error:
        save(root/'RESULT.json',dict(status='FAILED_OR_INCONCLUSIVE',mode=args.mode,error=str(error),retries=0,sample_exclusions=0))
        raise
    finally:
        save(root/'EVIDENCE.json',dict(files={str(p.relative_to(root)):identity(p) for p in sorted(root.rglob('*')) if p.is_file()}))


if __name__=='__main__':main()
