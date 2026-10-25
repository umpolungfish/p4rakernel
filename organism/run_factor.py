#!/usr/bin/env python3
"""Run the complete N-only organism factor entry and retain exact closure evidence."""
import argparse,hashlib,json,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--runtime',type=Path,required=True)
p.add_argument('--source',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--seconds',type=int,default=300)
a=p.parse_args();runtime=a.runtime.resolve();source=a.source.resolve();out=a.out.resolve()
out.mkdir(parents=True,exist_ok=False)
command=[str(runtime/'organism-factor'),str(source),str(runtime/'vgi_organism.so'),str(runtime/'factor_bridge.so'),str(a.seconds)]
started=time.monotonic()
report={'command':command,'input_boundary':'N alone','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'execution_limit_seconds':a.seconds,'verified':False,
        'images':{str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in
                  [runtime/'organism-factor',runtime/'factor_bridge.so',runtime/'vgi_organism.so']}}
try:
    result=subprocess.run(command,capture_output=True,timeout=a.seconds+30)
    (out/'stdout').write_bytes(result.stdout);(out/'stderr').write_bytes(result.stderr)
    report['exit_code']=result.returncode
    if result.returncode==0:
        body=json.loads(result.stdout);task=body['task'];factor=task.get('result')
        (out/'return.json').write_text(json.dumps(body)+'\n')
        report.update(boundary=task['boundary'],organism_actions=len(body['actions']),
            native_cycles=len(task['operations']),native_math_seconds=sum(o['seconds'] for o in task['operations']),
            native_preparation_seconds=task['preparation_seconds'],
            neural_instruction_updates=sum(len(x['neural_operations']) for x in body['actions']),
            task_feedback_updates=sum(len(x['task_operations']) for x in body['actions']))
        n=int(source.read_text())
        assert int(task['source'])==n
        for action in body['actions']:
            for operation in action['task_operations']:
                assert int(operation['retained_state']['source'])==n
        if factor:
            d=int(factor['p']);q=int(factor['q'])
            assert 1<d<n and n%d==0 and n//d==q and d*q==n
            assert factor['exact_product'] and factor['paired_boundary'] and factor['powerset_monad_laws']
            assert factor['inverse_returned'] and factor['native_resident_retained']
            assert all(dot['product_closed'] for dot in factor['braid_dots'])
            report.update(verified=True,p=str(d),q=str(q),producer=factor['producer'],
                actual_producing_port=factor['actual_producing_port'],banked_return=factor['banked_return'])
    else:report['error']=result.stderr.decode(errors='replace')[-3000:]
except subprocess.TimeoutExpired as error:
    (out/'stdout').write_bytes(error.stdout or b'');(out/'stderr').write_bytes(error.stderr or b'')
    report['timeout']=True
finally:
    report['process_seconds']=time.monotonic()-started
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['images','command']}),flush=True)
