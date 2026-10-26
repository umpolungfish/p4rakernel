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
return_limit_seconds=300
def return_markers():
    markers={}
    for line in (out/'stderr').read_text(errors='replace').splitlines(keepends=True):
        if not line.endswith('\n'):continue
        fields=line.split()
        if len(fields)==3 and fields[0]=='ORGANISM_RETURN_BEGIN':
            elapsed,limit=map(int,fields[1:])
            assert elapsed>=0 and limit==a.seconds*1000
            markers['native_execution_seconds']=elapsed/1000
        elif len(fields)==2 and fields[0]=='ORGANISM_RETURN_END':
            markers['native_return_seconds']=int(fields[1])/1000
    return markers
report={'command':command,'input_boundary':'N alone','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'execution_limit_seconds':a.seconds,'return_limit_seconds':return_limit_seconds,'verified':False,
        'images':{str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in
                  [runtime/'organism-factor',runtime/'factor_bridge.so',runtime/'vgi_organism.so']}}
try:
    environment=os.environ.copy();environment['ORGANISM_FACTOR_BUDGET_SECONDS']=str(a.seconds)
    with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
        process=subprocess.Popen(command,stdout=stdout,stderr=stderr,env=environment)
        identity={}
        try:
            identity={'process_start_ticks':Path(f'/proc/{process.pid}/stat').read_text().rsplit(')',1)[1].split()[19],
                      'pid_namespace':os.readlink('/proc/self/ns/pid')}
        except (OSError,IndexError):pass
        active={'status':'running_at_record','pid':process.pid,'phase':'execution',
            'command':command,'execution_limit_seconds':a.seconds,**identity}
        (out/'active.json').write_text(json.dumps(active,indent=2)+'\n')
        returning=None
        try:
            while True:
                markers=return_markers()
                if returning is None and 'native_execution_seconds' in markers:
                    returning=time.monotonic()
                    active.update(phase='return',return_limit_seconds=return_limit_seconds,**markers)
                    (out/'active.json').write_text(json.dumps(active,indent=2)+'\n')
                deadline=(returning+return_limit_seconds) if returning is not None else started+a.seconds+30
                remaining=deadline-time.monotonic()
                if remaining<=0:raise subprocess.TimeoutExpired(command,a.seconds if returning is None else return_limit_seconds)
                try:
                    code=process.wait(timeout=min(1,remaining));break
                except subprocess.TimeoutExpired:pass
        except subprocess.TimeoutExpired:
            process.kill();process.wait();raise
        report.update(return_markers())
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
            projected_views=0
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
                    if transition.get('zero_extended_view'):
                        assert transition['operation']=='native-view-reentry'
                        view=torus['native_views'][transition['native_view_index']]
                        old_p=numeral(previous['p']);old_q=numeral(previous['q'])
                        left,right=((old_p+old_q)//2,abs(old_p-old_q)//2) if view['conjugate']=='T' else (old_p,old_q)
                        values=[]
                        for value,coordinate in [(left,view['left']),(right,view['right'])]:
                            cells=coordinate['cells']
                            for i in range(max(value.bit_length(),len(cells))):
                                cell=cells[i] if i<len(cells) else 'F'
                                if cell=='T':value|=1<<i
                                elif cell=='F':value&=~(1<<i)
                                else:assert cell in ('N','B')
                            values.append(value)
                        left,right=values
                        expected=(abs(left-right) if old_p<=old_q else left+right) if view['conjugate']=='T' else left
                        expected=((expected&~7)|(old_p&7))%modulus
                        assert numeral(transition['after_p'])==expected
                        assert numeral(transition['after_q'])==n*pow(expected,-1,modulus)%modulus
                        projected_views+=1
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
            if projected_views:
                assert projected_views==report['native_view_reentries']
                report.update(native_view_projection_verified=True,zero_extended_native_views=projected_views)
            if torus.get('native_view_action_same_arm'):
                continued=0
                for operation in task['operations']:
                    event=operation.get('toroidal_operation',{})
                    if projection:=event.get('native_view_reentry'):
                        assert event['arm']==projection['arm']
                        before=event['transition']['before']
                        after=projection['transition']
                        assert numeral(before['p'])==numeral(after['after_p'])
                        assert numeral(before['q'])==numeral(after['after_q'])
                        assert numeral(event['clock'])==numeral(projection['clock'])+1
                        continued+=1
                    if 'arm' in event and 'learning_context' in operation:
                        context=operation['learning_context']
                        if operation.get('produced'):
                            # Closure installs the emitted divisor in its own
                            # odd coset before the final learner observation.
                            fields={f['name']:f['word'] for f in context['fields']}
                            p_value=numeral(fields['p']);q_value=numeral(fields['q'])
                            assert 1<p_value<n and p_value*q_value==n
                        else:assert context['arm']==event['arm']
                report.update(native_view_action_same_arm_verified=True,continued_native_view_actions=continued)
            if stark:=torus.get('stark_rotation'):
                from math import gcd
                dimension=stark['dimension'];trace=numeral(stark['trace'])
                assert dimension==n.bit_length() and trace==dimension-1
                def unit(value):return (numeral(value['a']),numeral(value['b']))
                def multiply(x,y):
                    a,b=x;c,d=y
                    return ((a*c-b*d)%n,(a*d+b*c+trace*b*d)%n)
                def conjugate(x):
                    a,b=x
                    return ((a+trace*b)%n,(-b)%n)
                def power(x,k):
                    out=(1,0)
                    while k:
                        if k&1:out=multiply(out,x)
                        x=multiply(x,x);k>>=1
                    return out
                state=(0,1);positive=1;negative=0;by_clock={}
                retained=[(state,1)];retained_comparisons=0
                for event in stark['events']:
                    assert unit(event['before'])==state
                    assert (numeral(event['before_positive']),numeral(event['before_negative']))==(positive,negative)
                    k=numeral(event['power']);port=event['port'];reverse=port in (0,4)
                    assert event['reverse']==reverse
                    if port in (2,5):
                        expected=power(state,k-1);positive*=k;negative*=k
                    else:
                        assert k==1
                        expected=conjugate((0,1)) if reverse else (0,1)
                        if reverse:negative+=k
                        else:positive+=k
                    operator=unit(event['operator']);inverse=unit(event['inverse'])
                    assert operator==expected and inverse==conjugate(operator)
                    assert multiply(operator,inverse)==(1,0)
                    after=unit(event['after'])
                    assert after==multiply(state,operator)
                    assert unit(event['recovered'])==state==multiply(after,inverse)
                    a_value,b_value=after
                    assert a_value*a_value+trace*a_value*b_value+b_value*b_value==n*numeral(event['norm_carry'])+1
                    assert (numeral(event['positive']),numeral(event['negative']))==(positive,negative)
                    for readout in event['readouts']:
                        expected=b_value if readout['kind']=='epsilon_coefficient' else (2*a_value+trace*b_value-2)%n
                        assert numeral(readout['value'])==expected
                        assert numeral(readout['gcd'])==gcd(expected,n)
                    if 'retained_units' in stark:
                        if observation:=event.get('retained_readout'):
                            assert observation['comparisons']==len(retained)
                            product=1;norms=[];zero=0;same=0;distinct=0
                            for index,(old,winding) in enumerate(retained):
                                a_delta=(a_value-old[0])%n;b_delta=(b_value-old[1])%n
                                norm=(a_delta*a_delta+trace*a_delta*b_delta+b_delta*b_delta)%n
                                relative=multiply(after,conjugate(old))
                                assert norm==(2-2*relative[0]-trace*relative[1])%n
                                if norm:
                                    product=product*norm%n;norms.append((index,norm))
                                else:
                                    zero+=1
                                    if after==old:
                                        if positive-negative==winding:same+=1
                                        else:distinct+=1
                            assert observation['zero_norms']==zero
                            assert observation['nonzero_norms']==len(norms)
                            assert observation['same_unit_same_winding']==same
                            assert observation['same_unit_distinct_winding']==distinct
                            divisor=gcd(product,n)
                            assert numeral(observation['product_residue'])==product
                            assert numeral(observation['gcd'])==divisor
                            split=observation['split_readouts']
                            for position,readout in enumerate(split):
                                index,norm=norms[position]
                                assert readout['index']==index
                                assert numeral(readout['gcd'])==gcd(norm,n)
                                if position+1<len(split):assert gcd(norm,n)==1
                            if divisor==n:
                                assert split and 1<numeral(split[-1]['gcd'])<n
                                divisor=numeral(split[-1]['gcd'])
                            else:assert not split
                            if divisor>1:
                                assert factor and divisor in (int(factor['p']),int(factor['q']))
                            retained_comparisons+=len(retained)
                        else:
                            assert any(1<numeral(r['gcd'])<n for r in event['readouts'])
                        retained.append((after,positive-negative))
                    by_clock[numeral(event['clock'])]=after;state=after
                paired=0;frames=[9]*len(torus['arms']);products=[1]*len(frames)
                for operation in task['operations']:
                    event=operation.get('toroidal_operation',{})
                    if transition:=event.get('stark_paired_transition'):
                        after=by_clock[numeral(event['clock'])-1]
                        frame=(1+8*sum(after))%modulus
                        multiplier=frame
                        if torus.get('stark_frame_transport'):
                            arm=event['arm']
                            assert numeral(transition['before_unit_frame'])==frames[arm]
                            assert numeral(transition['after_unit_frame'])==frame
                            multiplier=frame*pow(frames[arm],-1,modulus)%modulus
                            products[arm]=products[arm]*multiplier%modulus
                            assert products[arm]==frame*pow(9,-1,modulus)%modulus
                            frames[arm]=frame
                        inverse=pow(multiplier,-1,modulus)
                        assert numeral(transition['multiplier'])==multiplier
                        assert numeral(transition['inverse_multiplier'])==inverse
                        before=transition['before'];selected=event['transition']
                        assert numeral(before['p'])==numeral(selected['after_p'])
                        assert numeral(before['q'])==numeral(selected['after_q'])
                        assert numeral(transition['after_p'])==numeral(before['p'])*multiplier%modulus
                        assert numeral(transition['after_q'])==numeral(before['q'])*inverse%modulus
                        paired+=1
                assert paired==len(stark['events'])
                if torus.get('stark_frame_transport'):
                    assert [numeral(a['stark_frame']) for a in torus['arms']]==frames
                    report['stark_frame_transport_verified']=True
                assert unit(stark['state'])==state
                report.update(stark_rotation_verified=True,stark_paired_rotations=paired)
                if 'retained_units' in stark:
                    assert stark['retained_units']==len(retained)
                    report.update(retained_unit_readout_verified=True,retained_unit_comparisons=retained_comparisons)
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
        context_records=0;context_tokens=0
        for action in body['actions']:
            for operation in action['task_operations']:
                assert int(operation['retained_state']['source'])==n
                event=operation['retained_state'].get('operation') or {}
                context=event.get('learning_context')
                if context is not None:
                    tokens=operation['learning_context_tokens'];at=3
                    assert tokens[:3]==[256,85,context['arm']]
                    expected_names=['source','p','q','height','negative','positive_turns','negative_turns',
                                    'clock','membership','evidence','grid']
                    if context['schema']=='toroidal-learning-context-v2':
                        expected_names+=['execution_changed','logical_reentry','paired_progress',
                                         'relation_conflict','produced','task_feedback']
                    assert [f['name'] for f in context['fields']]==expected_names
                    decoded={}
                    for index,field in enumerate(context['fields']):
                        assert tokens[at]==index;at+=1
                        width=int.from_bytes(bytes(tokens[at:at+8]),'little');at+=8
                        cells=[]
                        for _ in range((width+1)//2):
                            value=tokens[at]-266;at+=1
                            assert 0<=value<16
                            cells.extend(['N','T','F','B'][(value>>shift)&3] for shift in [0,2])
                        assert cells[:width]==field['word']['cells']
                        decoded[field['name']]=field['word']
                    assert tokens[at:]==[257]
                    assert numeral(decoded['source'])==n
                    left=numeral(decoded['p']);right=numeral(decoded['q'])
                    sign=numeral(decoded['negative']);assert sign in (0,1)
                    assert left*right==n+(-1 if sign else 1)*numeral(decoded['height'])*(1<<n.bit_length())
                    if event.get('feedback_basis')=='source-arithmetic-v1':
                        observations=event['feedback_observations']
                        rails={'N':0,'T':1,'F':2,'B':3}
                        def joined(*values):
                            value=0
                            for v in values:value|=rails[v]
                            return ['N','T','F','B'][value]
                        torus_event=event['toroidal_operation']
                        assert observations['execution_changed']==('T' if event['changed'] else 'N')
                        assert observations['paired_progress']==joined(
                            torus_event.get('evidence','N'),
                            torus_event.get('native_view_reentry',{}).get('evidence','N'))
                        assert observations['relation_conflict']==('F' if event['conflict'] else 'N')
                        assert observations['produced']==('T' if event['produced'] else 'N')
                        logical=event.get('logical_reentry',[])
                        if logical:
                            mask=numeral(logical[-1]['after'])
                            assert observations['logical_reentry']==['N','T','F','B'][(mask>>1)&3]
                        assert event['feedback']==joined(observations['paired_progress'],
                            observations['relation_conflict'],observations['produced'])
                        assert observations['task_feedback']==event['feedback']
                        for name,value in observations.items():
                            assert decoded[name]['cells']==[value]
                    context_records+=1;context_tokens+=len(tokens)
        if context_records:
            learner=body['learner']
            assert learner['task_context_records']==context_records
            assert learner['task_context_tokens']==context_tokens
            assert learner['task_context_optimizer_updates']==context_records
            report.update(arithmetic_feedback_verified=all(e.get('feedback_basis')=='source-arithmetic-v1' for e in task['operations']),
                          paired_learning_context_verified=True,task_context_records=context_records,
                          task_context_tokens=context_tokens,task_context_optimizer_updates=learner['task_context_optimizer_updates'])
        polynomial_actions=task.get('square_polynomial_actions',[])
        if polynomial_actions:
            paired_states=set()
            for arm in task['toroidal_division']['arms']:
                paired_states.add((numeral(arm['origin_p']),numeral(arm['origin_q'])))
                paired_states.update((numeral(t['after_p']),numeral(t['after_q'])) for t in arm['ancestry'])
            clocks={numeral(o['clock']) for o in task['toroidal_division']['observations']}
            families={};previous_signs={};changed=0;held=0
            for action in polynomial_actions:
                assert int(action['source'])==n
                a=int(action['a']);before=int(action['before_b']);after=int(action['after_b'])
                terms=list(map(int,action['terms']));signs=action['counter_signs'];width=len(terms)
                frame=action['frame'];family=action['family']
                assert family not in families or families[family]==frame
                families[family]=frame
                if family in previous_signs:
                    expected=previous_signs[family].copy();position=1
                    while position<len(expected) and expected[position]:expected[position]=False;position+=1
                    assert position<len(expected);expected[position]=True
                    assert signs==expected
                else:assert signs==[False]*width
                previous_signs[family]=signs
                left=numeral(frame['p']);right=numeral(frame['q'])
                assert (left,right) in paired_states and left*right%(1<<n.bit_length())==n
                assert numeral(frame['clock']) in clocks
                permutation=list(range(width))
                assert sorted(frame['axes'])==list(range(12))
                for i,axis in enumerate(frame['axes']):
                    first=i%width;second=axis%width
                    permutation[first],permutation[second]=permutation[second],permutation[first]
                assert action['permutation']==permutation
                product=1;flips=[]
                for field in action['fields']:
                    prime=field['prime'];product*=prime
                    assert field['p_residue']==left%prime and field['q_residue']==right%prime
                    if field['inverse'] is None:
                        assert right%prime==0 and field['unit'] is None and field['character'] is None
                        nonunit=True;flip=False
                    else:
                        assert right*field['inverse']%prime==1
                        assert field['unit']==left*field['inverse']%prime
                        character=pow(field['unit'],(prime-1)//2,prime)
                        assert field['character']==character
                        nonunit=character==0;flip=character==prime-1
                    assert field['held_nonunit']==nonunit and field['flip']==flip
                    flips.append(flip);held+=nonunit
                assert product==a and action['flips']==flips
                transported=[signs[at]^flip for at,flip in zip(permutation,flips)]
                assert action['after_signs']==transported and action['recovered_signs']==signs
                assert sum((-term if sign else term) for term,sign in zip(terms,signs))%a==before
                assert sum((-term if sign else term) for term,sign in zip(terms,transported))%a==after
                assert before*before%a==after*after%a==n%a
                assert action['changed_b']==(before!=after)
                assert action['inverse_verified'] and action['source_congruence_verified']
                changed+=before!=after
            report.update(root_sign_transport_verified=True,root_sign_actions=len(polynomial_actions),
                          root_sign_families=len(families),root_sign_changed_polynomials=changed,
                          root_sign_held_field_observations=held)
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
