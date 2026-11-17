#!/usr/bin/env python3
"""Tool accounting fixture only; no ANL or solver execution."""
import json,os,resource,subprocess,sys,time

def raw(usage):return {name:getattr(usage,name) for name in dir(usage) if name.startswith('ru_')}
if '--child' in sys.argv:
    allocation=bytearray(24*1024*1024)
    for offset in range(0,len(allocation),4096):allocation[offset]=1
    start=time.process_time();total=0
    while time.process_time()-start<0.25:
        for i in range(1000):total=(total+i)%104729
    print(json.dumps(dict(intended_allocation_bytes=len(allocation),cpu_loop_seconds=0.25,checksum=total,self_usage=raw(resource.getrusage(resource.RUSAGE_SELF)))))
else:
    child=subprocess.Popen([sys.executable,__file__,'--child'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    pid,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
    stdout=child.stdout.read();stderr=child.stderr.read()
    print(json.dumps(dict(child_argv=child.args,child_exit=child.returncode,child_stdout=stdout.decode(),child_stderr=stderr.decode(),child_wait4=raw(usage),parent_self_usage=raw(resource.getrusage(resource.RUSAGE_SELF)),wait_behavior='parent waited its single child with wait4 before exiting')))
