"""Replay the restricted N-only prime torus/SIC computation."""
from math import gcd,isqrt

def audit_binary(image):
    import subprocess,hashlib
    from pathlib import Path
    image=Path(image)
    symbols=subprocess.run(['nm','-C',str(image)],capture_output=True,text=True,check=True).stdout
    patterns=['factor_synthesis::','glut_fold::','glut_correlation::','dialectic_','mpqs','pollard','brent','gpu_ecm::']
    counts={p:sum(p in s.lower() for s in symbols.splitlines()) for p in patterns}
    restricted=sum('prime_torus_sic::' in s for s in symbols.splitlines())
    assert restricted>0 and not any(counts.values())
    return dict(kind='compiled-symbol-scope',image=str(image),sha256=hashlib.sha256(image.read_bytes()).hexdigest(),
                restricted_symbols=restricted,forbidden_pattern_counts=counts)

def verify_context(event,tokens,n):
    context=event['learning_context']
    assert context['schema']=='prime-torus-learning-context-v1'
    assert tokens[:3]==[256,85,context['arm']] and context['arm']==event['port']%3
    expected={'source':n,'torus_x':int(event['after'][0]),'torus_y':int(event['after'][1]),
              'torus_z':int(event['after'][2]),'stage':event['stage'],'bound':event['bound'],
              'reentry_mask':event['reentry_state'],'pending_prime':event['pending_prime'],
              'pending_repetitions':event['pending_repetitions']}
    assert [f['name'] for f in context['fields']]==list(expected)
    at=3
    for index,field in enumerate(context['fields']):
        assert tokens[at]==index;at+=1
        width=int.from_bytes(bytes(tokens[at:at+8]),'little');at+=8;cells=[]
        for _ in range((width+1)//2):
            packed=tokens[at]-266;at+=1;assert 0<=packed<16
            cells.extend(['N','T','F','B'][(packed>>i)&3] for i in (0,2))
        cells=cells[:width]
        assert cells==field['word']['cells'] and all(c in ('T','F') for c in cells)
        value=sum((c=='T')<<i for i,c in enumerate(cells))
        assert value==int(field['word']['numeral'])==expected[field['name']]
    assert tokens[at:]==[257]
    return True

def verify(task,n):
    assert task['schema'] in ('prime-torus-sic-v1','prime-torus-sic-v2') and task['construction']=='prime-torus-sic'
    version2=task['schema']=='prime-torus-sic-v2'
    assert task['error'] is None
    assert task['allowed_operations']==['prime-braid-windings','horn-spindle-sphere-inner-return','full-SIC-dual']
    vec=lambda rows:[tuple(map(int,z)) for z in rows]
    point=lambda row:tuple(map(int,row))
    def gram(z):return [(a*c+b*d,a*d-b*c) for a,b in z for c,d in z]
    projectors=[gram(vec(ray)) for ray in task['preparation']['rays']]
    assert task['preparation']['base']==['-15','-8','17']
    assert task['preparation']['fractional_bits']==2*n.bit_length()+16
    def norm(p):return (p[0]**2+p[1]**2-p[2]**2)%n==0
    def compose(a,b):
        return ((a[0]*b[0]-a[1]*b[1])%n,(a[0]*b[1]+a[1]*b[0])%n,a[2]*b[2]%n)
    def power(p,k):
        z=(1,0,1)
        while k:
            if k&1:z=compose(z,p)
            p=compose(p,p);k>>=1
        return z
    def read(r,p):
        assert point(r['point'])==p and norm(p) and r['norm_verified']
        x,y,z=p;direction=(x*z%n,y*z%n,0);normal=(x*x%n,x*y%n,y*z%n)
        plus=tuple((a+b)%n for a,b in zip(normal,direction));minus=tuple((a-b)%n for a,b in zip(normal,direction))
        assert point(r['direction'])==direction and point(r['normal'])==normal
        assert point(r['sphere_inner_plus'])==plus and point(r['sphere_inner_minus'])==minus
        assert point(r['returned_direction'])==tuple((a-b)*pow(2,-1,n)%n for a,b in zip(plus,minus))==direction
        assert point(r['restored_normal'])==tuple((a+b)*pow(2,-1,n)%n for a,b in zip(plus,minus))==normal
        for frame,(name,R) in zip(r['frames'],(('horn',2),('spindle',1),('sphere',0))):
            assert frame['name']==name and frame['R']==R and frame['r']==2
            assert point(frame['point'])==tuple((R*a+2*b)%n for a,b in zip(direction,normal))
        state=[((direction[0]-z*z)%n,0),(0,direction[1]),(z*z%n,0),(1,0)]
        assert vec(r['amplitudes'])==state
        g=gram(state);assert vec(r['gram'])==g
        masses=[sum(a*c+b*d for (a,b),(c,d) in zip(projector,g)) for projector in projectors]
        assert list(map(int,r['mass_numerators']))==masses
        den=int(r['dual_denominator']);assert den>0
        back=vec(r['dual_numerators']);assert back==[(a*den,b*den) for a,b in g]
        witnesses=[back[3][0]//den,-back[7][1]//den,(back[3][0]+2*back[11][0])//den%n,back[11][0]//den]
        assert list(map(int,r['witnesses']))==witnesses
        divisors=[gcd(v,n) for v in witnesses];assert list(map(int,r['gcds']))==divisors
        assert r['exact_sic_return']
        return [d for d in divisors if 1<d<n]
    largest=max((p for event in task['operations'] for p in event['prime_word']),default=2)
    prime_flags=bytearray(b'\x01')*(largest+1);prime_flags[:2]=b'\x00\x00'
    for p in range(2,isqrt(largest)+1):
        if prime_flags[p]:prime_flags[p*p:largest+1:p]=b'\x00'*((largest-p*p)//p+1)
    state=((n-15)%n,(n-8)%n,17)
    assert point(task['initial_point'])==state and norm(state)
    stage=0;bound=n.bit_length()**2;retained=[];steps=0;valid=[]
    reentries=task.get('logical_reentry',[]) if version2 else []
    reentry_at=0;mask=0;terminal_count=0;conjugations=0
    def apply_reentries(index,state,mask,at):
        nonlocal conjugations
        while at<len(reentries) and reentries[at]['at_operation']==index:
            r=reentries[at];a,b,c,k=r['before'],r['permuted'],r['after'],r['kind']
            assert a==mask and 0<=a<16 and 0<=b<16 and 0<=c<16
            assert b==((a&1)<<1)|((a&2)>>1)|((a&4)<<1)|((a&8)>>1)
            if k==2:
                assert a==15
                expected=(~(((a&1)<<3)|((a&2)<<1)|((a&4)>>1)|((a&8)>>3)))&15
            else:
                assert k==1 and a!=15
                expected=a|next(1<<i for i in range(4) if not a&(1<<i))
            assert c==expected and point(r['point_before'])==state
            flip=bool(a&4)!=bool(c&4);assert r['conjugated']==flip
            if flip:state=(state[0],-state[1]%n,state[2]);conjugations+=1
            assert point(r['point_after'])==state and norm(state)
            mask=c;at+=1
        return state,mask,at
    for index,event in enumerate(task['operations']):
        state,mask,reentry_at=apply_reentries(index,state,mask,reentry_at)
        assert point(event['before'])==state
        if version2:assert event['reentry_state']==mask and event['reentry_count']==reentry_at
        changes={c['offset']:c for c in event['stage_changes']}
        terminals={r['offset']:r for r in event.get('stage_terminals',[])}
        states=[]
        for offset in range(len(event['prime_word'])+1):
            if offset in terminals:
                r=terminals[offset];assert r['stage']==stage and r['bound']==bound
                emitted=read(r['readout'],state);valid.extend(emitted);terminal_count+=1
                if offset not in changes:assert emitted and task['result'] is not None
            if offset in changes:
                if version2:assert offset in terminals
                change=changes[offset];stage+=1;bound*=2;t=4+stage
                state=((1-t*t)%n,2*t%n,(1+t*t)%n);retained=[]
                if version2:
                    assert change['reentry_state']==mask and change['chirality_conjugated']==bool(mask&4)
                    if mask&4:state=(state[0],-state[1]%n,state[2])
                assert change['stage']==stage and change['bound']==bound
                assert int(change['chart_parameter'])==t and point(change['point'])==state
            if offset==len(event['prime_word']):break
            prime=event['prime_word'][offset]
            assert prime>=2 and prime<=bound
            assert prime_flags[prime]
            state=power(state,prime);assert norm(state)
            states.append(state);retained.append(prime);steps+=1
        assert event['stage']==stage and event['bound']==bound and point(event['after'])==state
        valid.extend(read(event['sic_readout'],state))
        for cut in event['prefix_readouts']:
            valid.extend(read(cut['readout'],states[cut['prefix']-1]))
    state,mask,reentry_at=apply_reentries(len(task['operations']),state,mask,reentry_at)
    if version2:assert reentry_at==len(reentries) and task['reentry_state']==mask
    assert point(task['point'])==state and task['retained_prime_word']==retained
    assert task['stage']==stage and task['bound']==bound
    result=task['result']
    out=dict(restricted_construction_verified=True,prime_braid_steps=steps,
             torus_sic_readouts=len(task['operations']),stage_terminal_readouts=terminal_count,
             restricted_reentry_operations=reentry_at,restricted_reentry_conjugations=conjugations)
    if result:
        p,q=int(result['p']),int(result['q'])
        assert p in valid and 1<p<n and n%p==0 and n//p==q and p*q==n
        assert result['exact_product'] and result['paired_boundary'] and result['producer']=='prime-torus-sic'
        assert result['remainder']=='0' and int(result['product'])==n
        out.update(verified=True,p=str(p),q=str(q),producer=result['producer'])
    return out
