#!/usr/bin/env python3
"""Portable memory validation with explicit tools and independently frozen expectations."""
from pathlib import Path
import argparse,ast,gzip,hashlib,json,os,platform,shlex,sys
sys.dont_write_bytecode=True
from capture import Runner,save
from oracle import Failure,Inconclusive,REVISION,need,strict,same,keys,sha,heap_sites,outcome,assert_execution,assert_trace,assert_pair_report,validate_trace
from reference_protocol import protocol
HERE=Path(__file__).resolve().parent
GROUPS=("static","bridge","pairs","controls","bounds","output-bounds")

def file_sha(path):
    digest=hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda:source.read(1048576),b""):digest.update(chunk)
    return digest.hexdigest()

def bounded_read(path,limit):
    with Path(path).open("rb") as source:data=source.read(limit+1)
    need(len(data)<=limit,"file bound exceeded: "+str(path))
    return data

def generated_input(row):
    if row["kind"]=="empty-event-replay":
        events=[]
        for ordinal in range(row["pairs"]):
            events.extend([dict(kind="empty_open",empty=str(ordinal),site=dict(function=0,heap=0)),
                           dict(kind="empty_close",empty=str(ordinal),site=dict(function=0,heap=0))])
        if row["over"]:
            events.append(dict(kind="empty_open",empty=str(row["pairs"]),site=dict(function=0,heap=0)))
        template=strict((HERE/"replay/minimal-success.json").read_bytes())
        template["events"]=events
        if row["over"]:template["completion"]=dict(kind="trap",trap="index_out_of_bounds")
        return (json.dumps(template,sort_keys=True,separators=(",",":"))+"\n").encode()
    data=(HERE/row["base"]).read_bytes()
    need(len(data)<=row["bytes"],"negative fixture padding")
    return data+b" "*(row["bytes"]-len(data))

def audit():
    sealed=strict((HERE/"INTEGRITY.json").read_bytes())
    actual={str(p.relative_to(HERE)) for p in HERE.rglob("*") if p.is_file() and p.name!="INTEGRITY.json"}
    need(actual==set(sealed["files"]),"package file inventory changed")
    for name,item in sealed["files"].items():
        path=HERE/name
        need(path.is_file() and not path.is_symlink(),"missing or symlinked fixture: "+name)
        need(file_sha(path)==item["sha256"] and path.stat().st_size==item["bytes"],"package input changed: "+name)
    manifest=strict((HERE/"manifest.json").read_bytes())
    need(len(manifest["bridge"])==53 and len(manifest["static"])==18 and len(manifest["pairs"])==9,"fixture inventory")
    for collection in ('bridge','static','verify','pairs','raw','generators','output_bounds','compatibility','replay_invalid'):
        for row in manifest[collection]:
            for key in ('source','core','mir','path','plan','replay','expected_trace','expected','base'):
                if key in row and row[key]:
                    path=Path(row[key])
                    need(not path.is_absolute() and '..' not in path.parts and (HERE/path).is_file(),'nonportable/missing fixture: '+str(path))
    need((HERE/'cases/source/minimal.anl').is_file(),'missing replay boundary source')
    for graph in manifest['source_graphs']:
        need(graph['entry'] in [f['path'] for f in graph['files']],'source graph lacks entry')
        for item in graph['files']:
            path=HERE/item['path']
            need(file_sha(path)==item['sha256'] and path.stat().st_size==item['bytes'],'source graph differs')
    reasons=strict((HERE/"oracles/resource-reasons.json").read_bytes())
    for row in manifest["bridge"]:
        need(row["transitions"]==262144 and 0<=row["fuel"]<=1000000000,"resource policy drift")
        need(row["resource_reason"]==reasons.get(row["id"]),"resource reason binding")
        plan=strict((HERE/row["plan"]).read_bytes())
        responses=[]
        if row["replay"]:
            replay=strict((HERE/row["replay"]).read_bytes())
            responses=[e["response"] for e in replay["events"] if e["kind"]=="request"]
        need(same(plan,dict(schema="anl-memory-response-plan-v1",responses=responses,default="success")),"response plan differs")
        if row["expected_trace"]:
            trace=strict((HERE/row["expected_trace"]).read_bytes())
            core=strict((HERE/row["core"]).read_bytes())
            validate_trace(trace,row["profile"],heap_sites(core))
            need(same(outcome(trace["completion"]),row["expected_outcome"]),"trace/outcome differs")
    for row in manifest["generators"]:
        data=generated_input(row)
        need(len(data)==row["bytes"] and sha(data)==row["sha256"],"generated input digest differs")
    for row in manifest["output_bounds"]:
        with gzip.open(HERE/row["expected"],"rb") as source:data=source.read(8388609)
        need(len(data)==row["expected_bytes"] and sha(data)==row["expected_sha256"],"compressed expected trace differs")
        validate_trace(strict(data),manifest["allocation_profile"],{(0,0)})
    for path in HERE.glob("*.py"):ast.parse(path.read_text(),filename=str(path))
    return manifest

class Gate:
    def __init__(self,args,manifest):
        self.m=manifest;self.root=args.out.resolve();self.groups=args.groups.split(",");self.core_cache={};self.completed=[]
        need(set(self.groups)<=set(GROUPS) and len(set(self.groups))==len(self.groups),"unknown or repeated group")
        need(not self.root.exists() and self.root!=HERE and HERE not in self.root.parents,"use a fresh output directory outside the package")
        required=set()
        for group in self.groups:
            required.update({"static":("candidate","evidence"),"bridge":("candidate","evidence","exporter","pair_checker","reference","cc"),
                "pairs":("pair_checker","raw"),"controls":("candidate","evidence","exporter","pair_checker","cc"),"bounds":("evidence","pair_checker"),
                "output-bounds":("candidate","evidence","exporter","pair_checker","cc")}[group])
        arguments=dict(candidate=args.rust,evidence=args.evidence,exporter=args.exporter,pair_checker=args.pair,
                       reference=args.reference,cc=args.cc,raw=args.raw)
        self.binaries={};self.identities={}
        for name in sorted(required):
            need(arguments[name] is not None,"missing explicit tool: "+name)
            path=arguments[name].resolve(strict=True)
            need(path.is_file() and os.access(path,os.X_OK),"tool is not executable: "+name)
            self.binaries[name]=path;self.identities[name]=dict(path=str(path),sha256=file_sha(path),bytes=path.stat().st_size)
        self.package_sha256=file_sha(HERE/"INTEGRITY.json")
        self.python_identity=dict(path=str(Path(sys.executable).resolve()),sha256=file_sha(Path(sys.executable).resolve()))
        self.root.mkdir(parents=True,exist_ok=False)
        self.runner=Runner(self.root,manifest)
        # Bind shell launchers to this Python interpreter without relying on PATH shebang lookup.
        self.wrappers={}
        for name in ("cc_adapter","tool_spy"):
            path=self.root/(name+"-launcher")
            path.write_text("#!/bin/sh\nexec "+shlex.quote(sys.executable)+" "+shlex.quote(str(HERE/(name+".py")))+' "$@"\n')
            path.chmod(0o700);self.wrappers[name]=path
        save(self.root/"IDENTITY.json",dict(tools=self.identities,groups=self.groups,package_sha256=self.package_sha256,
            python=self.python_identity,
            host=dict(system=platform.system(),release=platform.release(),machine=platform.machine()),timings_collected=False))

    def source(self, row):
            return HERE / row["source"]

    def command(self, binary, command, path, *extra):
            return [self.binaries[binary],command,path,*extra]

    def trace_options(self, name, script):
            path = self.root / "traces" / (name + ".json")
            path.parent.mkdir(exist_ok=True)
            need(not path.exists(), "trace must be fresh")
            return path, dict(ANL_MEMORY_TRACE=path, ANL_MEMORY_REPLAY=script)

    def cc_options(self, name, handshake=None):
            values = dict(CC=self.wrappers["cc_adapter"], ANL_CORPUS_SCRATCH=self.root,
                          ANL_CORPUS_REAL_CC=self.binaries["cc"],
                          ANL_CORPUS_REAL_CC_SHA256=self.identities["cc"]["sha256"],
                          ANL_CORPUS_CC_LOG=self.root/"cc"/name)
            if handshake:
                values["ANL_CORPUS_CC_HANDSHAKE"] = handshake
            return values

    def spy_options(self, name):
            marker=self.root/"spies"/(name+".jsonl")
            marker.parent.mkdir(exist_ok=True)
            return marker,dict(CC=self.wrappers["tool_spy"],ANL_CORPUS_SPY_LOG=marker)

    def check_cc(self, name, memory=True, activated=False):
            root=self.root/"cc"/name
            records=[]
            for path in root.glob("call-*/command.json"):
                record=strict(path.read_bytes())
                need(record["real_cc_sha256"] == self.identities["cc"]["sha256"],"captured compiler identity")
                need(record["changed_arguments"] is False and record["exit"] == 0,"C adapter changed/failed command")
                for item in record["inputs"]:
                    data=bounded_read(path.parent/item["file"],67108864)
                    need(len(data)==item["bytes"] and sha(data)==item["sha256"],"C input capture changed")
                records.append(record)
            need(records,"no actual compiler captures")
            if memory:
                compile_calls=[r for r in records if any(i["path"].endswith(".c") for i in r["inputs"])]
                need(len(compile_calls)>=2,"memory program/runtime not separately compiled")
                for record in compile_calls:
                    need("-c" in record["argv"] and "-fno-lto" in record["argv"],"opaque runtime compilation flags")
                    need(("-DANL_MEMORY_EVIDENCE=1" in record["argv"])==activated,
                         "program/runtime evidence mode differs")
                    need(any(Path(item["path"]).name=="evidence.h" for item in record["inputs"])==activated,
                         "activated configuration capture differs")
                need(any("-c" not in r["argv"] for r in records),"no separate link")
            save(root/"capture-identity.json",dict(runtime="activated" if activated else "default",
                 compiler_sha256=self.identities["cc"]["sha256"],actual_inputs_retained=True,
                 records=[str(p.relative_to(root)) for p in root.glob("call-*/command.json")]))
            return records

    def validate_bundle(self,bundle,row):
            manifest=strict(bounded_read(bundle/"manifest.json",1048576))
            keys(manifest,("schema","semantic_revision","runtime","allocation_profile","compiler","files","sources"))
            need(manifest["schema"]=="anl-memory-evidence-bundle-v1" and manifest["semantic_revision"]==REVISION,
                 "bundle schema/revision")
            need(manifest["runtime"]=="default" and same(manifest["allocation_profile"],self.m["allocation_profile"]),
                 "bundle runtime/profile")
            keys(manifest["compiler"],("version","sha256","memory_evidence"))
            need(manifest["compiler"]["version"]=="0.1.0" and manifest["compiler"]["memory_evidence"] is True and
                 manifest["compiler"]["sha256"]==self.identities["exporter"]["sha256"],"bundle exporter identity")
            expected={n:dict(sha256=file_sha(bundle/n),bytes=(bundle/n).stat().st_size)
                      for n in ("core.json","mir.json","program.c","runtime.c","runtime.h")}
            need(same(manifest["files"],expected),"bundle file bindings differ")
            graph=next(g for g in self.m["source_graphs"] if g["entry"]==row["source"])
            sources=[dict(path_bytes_hex=os.fsencode((HERE/f["path"]).resolve()).hex(),sha256=f["sha256"],bytes=f["bytes"])
                     for f in graph["files"]]
            need(same(manifest["sources"],sources),"bundle source graph differs")

    def bind_cc_to_bundle(self,name,bundle):
            records=list((self.root/"cc"/name).glob("call-*/command.json"))
            if not records:return False
            seen=set()
            for path in records:
                for item in strict(path.read_bytes())["inputs"]:
                    basename=Path(item["path"]).name
                    if basename in ("program.c","runtime.c","runtime.h"):
                        need(item["sha256"]==file_sha(bundle/basename),"actual compiler input differs from retained default bundle: "+basename)
                        seen.add(basename)
            need(seen=={"program.c","runtime.c","runtime.h"},"missing actual C/header binding")
            save(self.root/"cc"/name/"bundle-binding.json",dict(bundle=str(bundle),
                identical_program_runtime_header=True,activated_config="retained separately as evidence.h when activated"))
            return True

    def dumped(self, source, name, expected_core=None):
            key=str(source)
            if key not in self.core_cache:
                result=self.runner.run("dump-"+name,self.command("candidate","dump-core",source))
                need(result["exit"]==0 and not result["stderr"],"source export failed")
                document=strict(result["stdout"])
                need(document["schema"]=="anl-core-v3" and document["semantic_revision"]==REVISION,"memory core envelope")
                need(same(document["allocation_profile"],self.m["allocation_profile"]),"source profile")
                if expected_core:
                    need(same(document,strict((HERE/expected_core).read_bytes())),"source core differs from sealed Core fixture")
                self.core_cache[key]=(result["folder"]/"stdout",document)
            if expected_core:
                need(same(self.core_cache[key][1],strict((HERE/expected_core).read_bytes())),
                     "cached source core differs from sealed Core fixture")
            return self.core_cache[key]

    def run_verify(self):
            for row in self.m["verify"]:
                for binary in ("candidate","evidence"):
                    label=row["name"]+"-"+binary+"-unsupported"
                    marker,options=self.spy_options(label)
                    options.update(ANL_MEMORY_TRACE="",ANL_MEMORY_REPLAY=self.root/"missing-replay")
                    result=self.runner.run(label,self.command(binary,"verify",self.source(row),
                                                              "--solver",self.wrappers["tool_spy"],"--json"),options)
                    need(result["exit"]==7,"memory verify status")
                    report=strict(result["stdout"])
                    for key,expected in dict(schema="anl-verify-v4",semantic_revision=REVISION,
                        verification_revision="anl-owned-buffers-unsupported-v1",trust="not_established",
                        type_checked=True,tested=False,dynamic_checks=False,contracts_erased=True,
                        compiler=None,solver=None,obligations=[]).items():
                        need(key in report and same(report[key],expected),"memory report field: "+key)
                    functions=report["functions"]
                    need(type(functions) is list and len(functions)==(1 if row["name"]=="dead-heap" else 2),
                         "all-loaded function metadata")
                    need([f["id"] for f in functions]==list(range(len(functions))),"function metadata IDs")
                    views=[f["view"] for f in functions if f["view"] is not None]
                    need(same(views,[] if row["name"]=="dead-heap" else [dict(mode="read",name="b")]),
                         "source view metadata")
                    need(len(report["sources"])==row.get("source_count",1),"all-loaded sources")
                    need(not marker.exists(),"unsupported verification started compiler/solver")

    def infrastructure(self, record):
            need(record["exit"]==4,"expected infrastructure refusal")
            need(record["stdout"]==b"","infrastructure source/native command published a value")

    def run_bounds(self):
            folder=self.root/"bounded-inputs";folder.mkdir()
            for row in self.m["generators"]:
                data=generated_input(row)
                need(sha(data)==row["sha256"],"generated bound input changed")
                path=folder/(row["name"]+".json");path.write_bytes(data)
                if row["kind"]=="empty-event-replay":
                    trace,env=self.trace_options(row["name"],path)
                    result=self.runner.run(row["name"],self.command("evidence","eval",HERE/row["source"],
                                                                     "--fuel",0),env)
                    if row["over"]:
                        self.infrastructure(result)
                        need(not trace.exists(),"over-limit event input began execution")
                    else:
                        assert_execution(result,dict(outcome="resource_limit"))
                        prefix=strict((HERE/"replay/minimal-success.json").read_bytes())
                        prefix.update(events=[],completion=dict(kind="resource_limit"))
                        assert_trace(bounded_read(trace,8388608),prefix,{(0,0)})
                    continue
                if row["kind"]=="padded-mir":
                    result=self.runner.run(row["name"],[self.binaries["pair_checker"],HERE/"cases/core/minimal.json",path])
                    assert_pair_report(result,"resource_limit" if row["over"] else "accepted",self.m["allocation_profile"])
                    continue
                trace,env=self.trace_options(row["name"],path if row["kind"]=="padded-replay" else HERE/"replay/minimal-success.json")
                if row["kind"]=="padded-core":
                    result=self.runner.run(row["name"],self.command("evidence","eval-core",path),env)
                    assert_execution(result,dict(outcome="resource_limit") if row["over"] else
                                     dict(outcome="value",type="i64",value="42"),wire=True)
                else:
                    result=self.runner.run(row["name"],self.command("evidence","eval",HERE/"cases/source/minimal.anl"),env)
                    if row["over"]:self.infrastructure(result)
                    else:assert_execution(result,dict(outcome="value",type="i64",value="42"))
                if row["over"]:need(not trace.exists(),"oversized input began evidence execution")
                else:assert_trace(bounded_read(trace,8388608),strict((HERE/"replay/minimal-success.json").read_bytes()),{(0,0)})

    def run_static(self):
        for row in self.m['static']:
            for binary in ('candidate','evidence'):
                marker,options=self.spy_options('static-'+row['name']+'-'+binary)
                options.update(ANL_MEMORY_TRACE='',ANL_MEMORY_REPLAY=self.root/'missing-replay')
                for command,expected in (('check',row['check_exit']),('eval',row['eval_exit'])):
                    result=self.runner.run(row['name']+'-'+binary+'-'+command,self.command(binary,command,self.source(row)),options)
                    need(result['exit']==expected and result['stdout']==b'','static/entry classification')
                    need(bool(result['stderr'])==(expected!=0),'static diagnostic classification')
                need(not marker.exists(),'static rejection started a tool')
        self.run_verify()

    def export(self,row,source,core_path):
        name=row['name'];bundle=self.root/'bundles'/name;bundle.parent.mkdir(exist_ok=True)
        result=self.runner.run('bundle-'+name,[self.binaries['exporter'],source,bundle])
        need(result['exit']==0 and not result['stdout'] and not result['stderr'],'bundle export failed')
        self.validate_bundle(bundle,row)
        need((bundle/'core.json').read_bytes()==core_path.read_bytes(),'actual source and exported Core differ')
        before={p.name:file_sha(p) for p in bundle.iterdir() if p.is_file()}
        result=self.runner.run('actual-pair-'+name,[self.binaries['pair_checker'],bundle/'core.json',bundle/'mir.json'])
        assert_pair_report(result,'accepted',self.m['allocation_profile']);need(not result['stderr'],'pair diagnostic')
        need(before=={p.name:file_sha(p) for p in bundle.iterdir() if p.is_file()},'bundle changed during checking')
        return bundle

    def reference(self,row,core):
        result=self.runner.run('reference-'+row['id'],[self.binaries['reference'],core,HERE/row['plan'],row['fuel'],row['transitions']])
        document=None if row['status']=='rejected' else strict(core.read_bytes())
        report=protocol(result,row,None if document is None else heap_sites(document))
        if report['status'] in ('transition_limit','error'):
            raise Inconclusive('reference '+report['status']+': '+report['reason'])
        need(report['status']==row['status'] and result['exit']==row['exit'],'reference classification differs')
        need(report['resource_reason']==row['resource_reason'],'reference resource reason differs')
        if row['expected_trace']:
            expected=strict((HERE/row['expected_trace']).read_bytes())
            need(same(report['trace'],expected),'reference trace/completion differs from independent oracle')
        else:
            need(report['allocation_profile'] is None and report['meter'] is None and report['trace'] is None,'rejected Core ran')
        return report

    def execution(self,result,row,wire=False,refusal_values=()):
        expected=row['expected_outcome']
        assert_execution(result,expected,wire=wire,refusal_values=refusal_values)
        need(bool(result['stderr'])==(expected['outcome']!='value'),'wire/source diagnostic classification')
        if row['resource_reason']:
            suffix=': resource_limit: '+self.m['resource_diagnostics'][row['resource_reason']]+'\n'
            need(result['stderr'].endswith(suffix.encode()),'evaluator resource reason differs')

    def run_bridge(self):
        for row in self.m['bridge']:
            name=row['name'];source=HERE/row['source'] if row['group']=='source' else None
            core=HERE/row['core'];bundle=None
            if source is not None:
                result=self.runner.run('check-'+name,self.command('candidate','check',source))
                need(result['exit']==0 and not result['stdout'] and not result['stderr'],'valid source rejected')
                core,document=self.dumped(source,name)
                need(core.read_bytes()==(HERE/row['core']).read_bytes(),'actual Core differs from accepted source artifact')
                bundle=self.export(row,source,core)
            report=self.reference(row,core)
            expected=row['expected_outcome']
            sites=None if row['status']=='rejected' else heap_sites(strict(core.read_bytes()))
            routes=[('eval',source),('eval-core',core)] if source is not None else [('eval-core',core)]
            for command,path in routes:
                label=row['id']+'-'+command
                trace,options=self.trace_options(label,HERE/row['replay'] if row['replay'] else None)
                result=self.runner.run(label,self.command('evidence',command,path,'--fuel',row['fuel']),options)
                self.execution(result,row,wire=command=='eval-core')
                if row['status']=='rejected':
                    need(not trace.exists(),'invalid Core emitted evidence')
                elif row['id']=='core-v3-scalar-embedding':
                    # The default scalar route ignores memory evidence controls by design.
                    need(not trace.exists(),'embedded scalar unexpectedly activated memory evidence')
                    need(report['trace']['events']==[],'scalar reference fabricated memory activity')
                else:
                    assert_trace(bounded_read(trace,8388608),strict((HERE/row['expected_trace']).read_bytes()),sites)
            if row['default']:
                for binary in ('candidate','evidence'):
                    command='eval' if source is not None else 'eval-core'
                    path=source if source is not None else core
                    result=self.runner.run(row['id']+'-'+binary+'-ordinary',self.command(binary,command,path,'--fuel',row['fuel']))
                    self.execution(result,row,wire=source is None,refusal_values=row.get('default_refusal_values',()))
            native_done=[]
            if source is not None and row['native']:
                need(row['status'] in ('value','trap'),'resource row must never run native')
                label=name+'-native-replay'
                trace,options=self.trace_options(label,HERE/row['replay']);options.update(self.cc_options(label))
                result=self.runner.run(label,self.command('evidence','run',source),options,timeout=self.m['native_timeout_seconds'])
                assert_execution(result,expected)
                assert_trace(bounded_read(trace,8388608),strict((HERE/row['expected_trace']).read_bytes()),sites)
                self.check_cc(label,activated=True);need(self.bind_cc_to_bundle(label,bundle),'missing native binding')
                native_done.append('evidence-replay')
                if row['default']:
                    for binary in ('candidate','evidence'):
                        label=name+'-'+binary+'-default-native'
                        result=self.runner.run(label,self.command(binary,'run',source),self.cc_options(label),timeout=self.m['native_timeout_seconds'])
                        assert_execution(result,expected,refusal_values=row.get('default_refusal_values',()))
                        self.check_cc(label);need(self.bind_cc_to_bundle(label,bundle),'missing default native binding')
                        native_done.append(binary+'-default')
            self.completed.append(dict(case=row['id'],status='PASS',reference_status=report['status'],
                exact_trace=row['expected_trace'] is not None,native_routes=native_done,
                native_exclusion=None if native_done else ('raw-Core fixture' if source is None else 'sealed interpreter/resource-boundary fixture')))
            save(self.root/'ROWS.json',self.completed)

    def run_pairs(self):
        for row in self.m['raw']:
            result=self.runner.run('raw-'+row['kind']+'-'+Path(row['path']).stem,[self.binaries['raw'],row['kind'],HERE/row['path']])
            report=strict(result['stdout']);keys(report,('raw_valid','reason'))
            need(result['exit']==0 and result['stderr']==b'' and report['raw_valid'] is True and report['reason']=='','raw typing judgment failed')
        for row in self.m['pairs']:
            result=self.runner.run('pair-'+row['name'],[self.binaries['pair_checker'],HERE/row['core'],HERE/row['mir']])
            assert_pair_report(result,row['status'],self.m['allocation_profile'])
            need(not result['stderr'],'pair diagnostic')

    def run_controls(self):
        zero=next(r for r in self.m["bridge"] if r["name"]=="zero-initializer-once")
        source=self.source(zero)
        expected=strict((HERE/zero["expected_trace"]).read_bytes())
        minimal=HERE/"cases/source/minimal.anl"
        script=HERE/"replay/minimal-success.json"
        raw,_=self.dumped(source,"activation-zero")
        for command,path in (("eval",source),("eval-core",raw),("run",source),("build",source)):
            label="default-ignores-"+command
            trace,env=self.trace_options(label,self.root/"missing-replay")
            extra=[]
            destination=self.root/(label+".exe")
            if command=="build":
                extra=["-o",destination]
            if command in ("run","build"):
                env.update(self.cc_options(label))
            result=self.runner.run(label,self.command("candidate",command,path,*extra),env)
            if command=="build":
                need(result["exit"]==0 and destination.is_file(),"default build did not ignore controls")
                direct=self.runner.run(label+"-execute",[destination])
                assert_execution(direct,outcome(expected["completion"]))
            else:
                assert_execution(result,outcome(expected["completion"]),wire=command=="eval-core")
            need(not trace.exists(),"default compiler consulted evidence controls")
            if command in ("run","build"):
                self.check_cc(label)
        for command in ("check","verify","dump-core","emit-c"):
            label="nonexecuting-ignores-"+command
            marker,env=self.spy_options(label)
            env.update(ANL_MEMORY_TRACE="",ANL_MEMORY_REPLAY="")
            extra=["--json"] if command=="verify" else []
            result=self.runner.run(label,self.command("evidence",command,source,*extra),env,
                stdout_limit=self.m["c_stdout_limit"] if command=="emit-c" else None)
            need(result["exit"]==(7 if command=="verify" else 0),"nonexecuting command activated controls")
            need(not marker.exists(),"nonexecuting command started a compiler")
        bundle=self.root/"ignored-control-export"
        result=self.runner.run("export-ignores-controls",[self.binaries["exporter"],source,bundle],
                               dict(ANL_MEMORY_TRACE="",ANL_MEMORY_REPLAY=""))
        need(result["exit"]==0 and (bundle/"runtime.c").is_file(),"export-only controls not ignored")
        self.validate_bundle(bundle,zero)
        need((bundle/"core.json").read_bytes()==raw.read_bytes(),"ignored-control exported Core differs")
        bundle_before={p.name:file_sha(p) for p in bundle.iterdir() if p.is_file()}
        pair=self.runner.run("ignored-control-actual-pair",[self.binaries["pair_checker"],bundle/"core.json",bundle/"mir.json"])
        assert_pair_report(pair,"accepted",self.m["allocation_profile"]);need(not pair["stderr"],"pair diagnostic")
        need(bundle_before=={p.name:file_sha(p) for p in bundle.iterdir() if p.is_file()},"ignored-control bundle changed")
        save(self.root/"ignored-export-identity.json",dict(runtime="default",activated_runtime=False,
             files={p.name:file_sha(p) for p in bundle.iterdir() if p.is_file()}))
        for name in ("scalar","tuple"):
            ordinary=next(r for r in self.m["compatibility"] if r["name"]==name)
            for command in ("eval","run"):
                label="ordinary-ignores-"+name+"-"+command
                env=dict(ANL_MEMORY_TRACE="",ANL_MEMORY_REPLAY="",CC=self.binaries["cc"])
                result=self.runner.run(label,self.command("evidence",command,self.source(ordinary)),env)
                assert_execution(result,dict(outcome="value",type="i64",value=ordinary["value"]))
        invalid_options={
            "replay-only":dict(ANL_MEMORY_REPLAY=script),
            "empty-trace":dict(ANL_MEMORY_TRACE=""),
            "empty-replay":dict(ANL_MEMORY_TRACE=self.root/"empty-replay-trace",ANL_MEMORY_REPLAY=""),
            "missing-parent":dict(ANL_MEMORY_TRACE=self.root/"absent-parent"/"trace.json"),
            "relative-trace":dict(ANL_MEMORY_TRACE="relative-memory-validation-trace.json"),
        }
        for name,env in invalid_options.items():
            result=self.runner.run("activation-invalid-"+name,self.command("evidence","eval",minimal),env)
            self.infrastructure(result)
        for row in self.m["replay_invalid"]:
            for command in ("eval","build"):
                label="invalid-replay-"+row["name"]+"-"+command
                trace,env=self.trace_options(label,HERE/row["replay"])
                marker,spy=self.spy_options(label);env.update(spy)
                destination=self.root/(label+".exe")
                sentinel=b"existing executable destination\n"
                extra=[]
                if command=="build":
                    destination.write_bytes(sentinel);extra=["-o",destination]
                result=self.runner.run(label,self.command("evidence",command,minimal,*extra),env)
                self.infrastructure(result)
                need(not trace.exists() and not marker.exists(),"invalid replay began execution/compiler")
                if command=="build":
                    need(destination.read_bytes()==sentinel,"invalid replay replaced existing output")
        good=strict(script.read_bytes())
        for name,events in (("wrong-actual-length",[]),("wrong-completion",good["events"])):
            trace,env=self.trace_options("unreachable-"+name,HERE/("replay/unreachable-"+name+".json"))
            result=self.runner.run("unreachable-"+name,self.command("evidence","eval",minimal),env)
            self.infrastructure(result)
            actual=validate_trace(strict(bounded_read(trace,8388608)),self.m["allocation_profile"],{(0,0)})
            need(same(actual["events"],events) and actual["completion"]["kind"]=="infrastructure",
                 "unreachable replay did not retain the expected infrastructure prefix")
        minimal_row=dict(name="controls-minimal",source="cases/source/minimal.anl")
        minimal_core,_=self.dumped(minimal,"controls-minimal")
        minimal_bundle=self.export(minimal_row,minimal,minimal_core)
        for variant in ("immutable-plan","exclusive-create-race"):
            label="captured-"+variant
            replay=self.root/(label+"-replay.json");replay.write_bytes(script.read_bytes())
            trace,env=self.trace_options(label,replay)
            env.update(self.cc_options(label))
            executable=self.root/(label+".exe")
            result=self.runner.run(label,self.command("evidence","build",minimal,"-o",executable),env)
            need(result["exit"]==0 and executable.is_file(),"evidence build failed")
            need(not trace.exists(),"build created embedded trace destination")
            self.check_cc(label,activated=True)
            need(self.bind_cc_to_bundle(label,minimal_bundle),"missing captured-plan native binding")
            replay.write_bytes(b"changed after successful build\n")
            save(self.root/(label+"-external-mutation.json"),dict(actor="corpus harness",
                 path=str(replay),sha256=file_sha(replay),purpose="prove immutable captured replay plan"))
            if variant=="exclusive-create-race":
                trace.write_bytes(b"external trace sentinel\n")
                before=trace.read_bytes()
                direct=self.runner.run(label+"-execute",[executable])
                self.infrastructure(direct)
                need(trace.read_bytes()==before,"exclusive-create failure overwrote trace")
            else:
                direct=self.runner.run(label+"-execute",[executable])
                assert_execution(direct,dict(outcome="value",type="i64",value="42"))
                assert_trace(bounded_read(trace,8388608),good,{(0,0)})
                before=trace.read_bytes()
                repeat=self.runner.run(label+"-second-execution",[executable])
                self.infrastructure(repeat)
                need(trace.read_bytes()==before,"second execution overwrote first trace")
        # Record-only mode is deterministic for the empty owner and requires no allocator assumption.
        for command in ("eval","run"):
            label="record-only-"+command
            trace,env=self.trace_options(label,HERE/zero["replay"])
            env.pop("ANL_MEMORY_REPLAY")
            if command=="run":env.update(self.cc_options(label))
            result=self.runner.run(label,self.command("evidence",command,source),env)
            assert_execution(result,outcome(expected["completion"]))
            assert_trace(bounded_read(trace,8388608),expected,{(0,0)})
            if command=="run":self.check_cc(label,activated=True)
        for label in ("default-ignores-run","default-ignores-build","record-only-run"):
            self.bind_cc_to_bundle(label,bundle)

    def run_output_bounds(self):
        for row in self.m['output_bounds']:
            source=HERE/row['source'];core,document=self.dumped(source,row['name'])
            bundle=self.export(row,source,core)
            need(heap_sites(document)=={(0,0)},'output-boundary sites differ')
            with gzip.open(HERE/row['expected'],'rb') as stream:expected=stream.read(8388609)
            need(len(expected)==row['expected_bytes'] and sha(expected)==row['expected_sha256'],'output oracle bytes')
            for route in ('eval','run'):
                label=row['name']+'-'+route;trace,options=self.trace_options(label,None)
                argv=self.command('evidence',route,source)
                if route=='eval':argv+=['--fuel',str(row['fuel'])]
                else:options.update(self.cc_options(label))
                result=self.runner.run(label,argv,options)
                if row['expected_exit']==0:assert_execution(result,dict(outcome='value',type='i64',value='32768'))
                else:
                    need(result['exit']==4 and result['stdout']==b'' and b'trace event bound exceeded' in result['stderr'],'wrong output-event exhaustion classification')
                assert_trace(bounded_read(trace,8388608),strict(expected),{(0,0)})
                if route=='run':
                    self.check_cc(label,activated=True);need(self.bind_cc_to_bundle(label,bundle),'missing output-boundary native binding')

    def finish(self):
        need(file_sha(HERE/"INTEGRITY.json")==self.package_sha256,"package integrity inventory changed")
        need(file_sha(self.python_identity["path"])==self.python_identity["sha256"],"Python interpreter changed")
        for name,item in self.identities.items():
            need(file_sha(item['path'])==item['sha256'],'tool changed: '+name)
        audit()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','gate'))
    parser.add_argument('--groups',default='static,bridge,pairs,controls')
    parser.add_argument('--out',type=Path)
    for name in ('rust','evidence','exporter','pair','raw','reference','cc'):parser.add_argument('--'+name,type=Path)
    args=parser.parse_args();manifest=audit()
    if args.mode=='audit':
        print(json.dumps(dict(status='PASS',source_rows=24,core_rows=29,project_commands_executed=0,timings_collected=False)))
        return 0
    need(args.out is not None,'--out is required for a fresh capture directory')
    gate=Gate(args,manifest);report=dict(status='RUNNING',requested_groups=gate.groups,completed_groups=[],
        historical_phases_not_reexecuted=['alias/publication faults','ABI-negative checks','host path/filename limitations and native non-UTF8 filename case','serialized trace-byte exhaustion'],
        retries=0,timings_collected=False,complete_language_or_os_acceptance=False)
    save(gate.root/'RESULT.json',report)
    try:
        for group in gate.groups:
            getattr(gate,'run_'+group.replace('-','_'))()
            report['completed_groups'].append(group);save(gate.root/'RESULT.json',report)
        report['status']='PASS'
    except (Exception,KeyboardInterrupt) as error:
        report['status']='INCONCLUSIVE' if isinstance(error,(Inconclusive,OSError,KeyboardInterrupt)) else 'FAIL'
        report['failure']=str(error)
    finally:
        try:gate.finish()
        except Exception as error:report['status']='INCONCLUSIVE';report['postcheck_failure']=str(error)
        report['commands']=gate.runner.records;report['bridge_rows']=gate.completed
        save(gate.root/'RESULT.json',report)
    print(json.dumps(dict(status=report['status'],output=str(gate.root),commands=len(gate.runner.records))))
    return 0 if report['status']=='PASS' else 2 if report['status']=='INCONCLUSIVE' else 1

if __name__=='__main__':raise SystemExit(main())
