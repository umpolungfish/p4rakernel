#!/usr/bin/env python3
"""Run the complete N-only organism factor entry and retain exact closure evidence."""
import argparse,hashlib,json,subprocess,time,os
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
    environment=os.environ.copy();environment['ORGANISM_FACTOR_BUDGET_SECONDS']=str(a.seconds)
    with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
        process=subprocess.Popen(command,stdout=stdout,stderr=stderr,env=environment)
        (out/'active.json').write_text(json.dumps({'status':'running_at_record','pid':process.pid,
            'command':command,'execution_limit_seconds':a.seconds},indent=2)+'\n')
        try:code=process.wait(timeout=a.seconds+30)
        except subprocess.TimeoutExpired:
            process.kill();process.wait();raise
    report['exit_code']=code
    if code==0:
        body=json.loads((out/'stdout').read_bytes());task=body['task'];factor=task.get('result')
        (out/'return.json').write_text(json.dumps(body)+'\n')
        report.update(boundary=task['boundary'],organism_actions=len(body['actions']),
            native_cycles=len(task['operations']),native_math_seconds=sum(o['seconds'] for o in task['operations']),
            native_preparation_seconds=task['preparation_seconds'],
            budget_exhausted=task.get('budget_exhausted',False),
            neural_instruction_updates=sum(len(x['neural_operations']) for x in body['actions']),
            task_feedback_updates=sum(len(x['task_operations']) for x in body['actions']))
        n=int(source.read_text())
        assert int(task['source'])==n
        if torus:=task.get('toroidal_division'):
            def numeral(value):
                cells=value['cells']
                assert all(c in ('T','F') for c in cells)
                decoded=sum((c=='T')<<i for i,c in enumerate(cells))
                assert decoded==int(value['numeral'])
                return decoded
            assert torus['carrier']=='BelnapWord' and numeral(torus['source'])==n
            if 'resident_identity' in torus:assert torus['resident_identity']==task['resident_identity']
            modulus=1<<torus['modulus_exponent']
            for arm in torus['arms']:
                left=numeral(arm['p']);right=numeral(arm['q'])
                height=arm['signed_product_height'];sign=height['negative']
                assert sign in ('T','F')
                signed=numeral(height['magnitude'])*(-1 if sign=='T' else 1)
                assert left*right==n+signed*modulus
                if 'square_view' in arm:
                    view=arm['square_view'];mid=numeral(view['midpoint']);gap=numeral(view['gap'])
                    assert mid*mid-gap*gap==left*right
                    assert (mid-gap,mid+gap)==tuple(sorted((left,right)))
                    assert view['p_is_lower']==('T' if left<=right else 'F')
                if 'origin_p' in arm:
                    forward=numeral(arm['positive_turns']);reverse=numeral(arm['negative_turns'])
                    step=numeral(torus['step']);back=numeral(torus['inverse_step'])
                    assert numeral(arm['origin_p'])*pow(step,forward,modulus)*pow(back,reverse,modulus)%modulus==left
                    assert numeral(arm['origin_q'])*pow(back,forward,modulus)*pow(step,reverse,modulus)%modulus==right
                    period=numeral(torus['orbit_period']);lift=arm['rotation_lift']
                    assert divmod(forward,period)==(numeral(lift['forward_full_turns']),numeral(lift['forward_phase']))
                    assert divmod(reverse,period)==(numeral(lift['reverse_full_turns']),numeral(lift['reverse_phase']))
                for transition in arm['ancestry']:
                    previous=transition['before']
                    delta=numeral(previous['height'])*(-1 if previous['negative']=='T' else 1)
                    assert numeral(previous['p'])*numeral(previous['q'])==n+delta*modulus
                    delta=numeral(transition['after_height'])*(-1 if transition['negative']=='T' else 1)
                    assert numeral(transition['after_p'])*numeral(transition['after_q'])==n+delta*modulus
                    if 'poloidal_pinch_half_turns' in transition:
                        at=numeral(transition['poloidal_pinch_half_turns'])
                        assert at%2==1
                        assert numeral(transition['poloidal_return_half_turns'])==at+1
            assert sorted(torus['axes'])==list(range(12))
            report['toroidal_transitions']=sum(len(arm['ancestry']) for arm in torus['arms'])
            report['toroidal_belnap_return_verified']=True
            report['toroidal_cell_decisions']=len(task.get('toroidal_cell_decisions',[]))
            report['joint_coordinate_views']=len(torus.get('native_views',[]))
            report['native_view_reentries']=sum(t['operation']=='native-view-reentry'
                for arm in torus['arms'] for t in arm['ancestry'])
            if 'reentry_state' in torus:
                events=[event for operation in task['operations'] for event in operation.get('logical_reentry',[])]
                events+=task.get('pending_logical_reentry',[])
                state=0
                for event in events:
                    before=numeral(event['before']);after=numeral(event['after'])
                    assert before==state and 0<=after<16 and event['inverse_verified']
                    kind=event['operation']
                    if kind=='permutation-reentry':expected=((before&5)<<1)|((before&10)>>1)
                    elif kind=='conflation-return':expected=15^(((before&1)<<3)|((before&2)<<1)|((before&4)>>1)|((before&8)>>3))
                    else:
                        assert kind=='inc-ascent'
                        expected=before
                        for bit in [1,2,4,8]:
                            if not expected&bit:expected|=bit;break
                    assert after==expected and event['atom_order']==['N','T','F','B']
                    assert event['TF_shadow']==['N','T','F','B'][(after>>1)&3]
                    assert event['designated']==bool(after&2)
                    state=after
                assert numeral(torus['reentry_state'])==state
                report['logical_reentries']=len(events)
                report['conflation_returns']=sum(e['operation']=='conflation-return' for e in events)
                report['logical_reentry_return_verified']=True
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
    else:report['error']=(out/'stderr').read_text(errors='replace')[-3000:]
except subprocess.TimeoutExpired:
    report['timeout']=True
finally:
    report['process_seconds']=time.monotonic()-started
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'active.json').write_text(json.dumps({'status':'terminal','receipt':str(out/'receipt.json')},indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['images','command']}),flush=True)
