"""Replay complete complex source-ring returns from the executing bank receipts."""
from math import gcd

def verify(task, n):
    prep=task.get('sic_geometry_preparation',{})
    if 'cyclic_source_word' in prep:
        import re,subprocess
        from pathlib import Path
        root=Path(__file__).resolve().parents[2]
        source=(root/'Vox/src/combined_factor.rs').read_text()
        table=re.findall(r'"([⊢⊣≻≺⋈⊙∈∋⊤⊥⊞⊡]+)"',re.search(r'pub const HEX_WORDS:.*?= \[(.*?)\];',source,re.S)[1])
        expected='⊢'+''.join(table[int(d,16)][1:-1] for d in format(n,'x'))+'⊣'
        assert prep['cyclic_source_word']==expected
        result=subprocess.run([str(root/'MoDoT/ask_native/target/x86_64-unknown-linux-gnu/release/ask'),'--rotat',expected],capture_output=True,text=True,check=True,timeout=60)
        rows=re.findall(r'^\s+(\d+)\s+(\S+)\s+([TNBF])\s+',result.stdout,re.M)
        def mask(name):return 15 if name=='A' else sum(v for c,v in [('T',1),('F',2),('t',4),('f',8)] if c in name)
        landings=[mask(row[1]) for row in rows]
        assert landings==prep['cyclic_source_landings'] and len(landings)==len(expected)
        for op in task['operations']:
            data=op['toroidal_operation'].get('geometric_sic')
            if data is None:continue
            phase=data['cyclic_source_phase']
            clock=next(int(f['word']['numeral']) for f in data['input_context']['fields'] if f['name']=='clock')
            cut=(clock if phase.get('cut_selector')=='retained-clock' else data['tick']-1)%len(expected)
            assert phase['cut']==cut and phase['modulus']==len(expected)
            assert phase['landing_runtime_mask']==landings[cut]
            assert phase['marked_channels']==[bool(landings[cut]&(1<<i)) for i in range(4)]
    def pairs(x): return [tuple(map(int,z)) for z in x]
    def add(a,b): return ((a[0]+b[0])%n,(a[1]+b[1])%n)
    def mul(a,b): return ((a[0]*b[0]-a[1]*b[1])%n,(a[0]*b[1]+a[1]*b[0])%n)
    def dot(a,b):
        z=(0,0)
        for x,y in zip(a,b):z=add(z,mul(x,y))
        return z
    def mm(a,b):return [dot(a[4*i:4*i+4],b[j::4]) for i in range(4) for j in range(4)]
    def mv(a,b):return [dot(a[4*i:4*i+4],b) for i in range(4)]
    eye=[(int(i==j),0) for i in range(4) for j in range(4)]
    def power(a,k):
        v=eye
        while k:
            if k&1:v=mm(v,a)
            a=mm(a,a);k//=2
        return v
    def prime_power(m):
        d=2
        while d*d<=m and m%d:d+=1
        if d*d>m:return m
        while m%d==0:m//=d
        return d if m==1 else None
    current=inv=base=None;origin=None;exponent=bound=1;count=crossings=0
    for operation in task['operations']:
        data=operation['toroidal_operation'].get('geometric_sic',{})
        r=data.get('source_return')
        if r is None:continue
        assert int(r['source'])==n
        frame=data['banked_frame'];den=int(data['action_denominator']);norm=int(frame['dual_normalization'][0])
        if r['stage']=='frame-nonunit':
            x={'operator_denominator':den,'dual_normalization':norm}[r['coordinate']]%n
            assert int(r['value'])==x and int(r['gcd'])==gcd(x,n)
            assert r['resident_bank_unchanged']
            continue
        count+=1;assert r['tick']==count
        f=[((a*pow(den,-1,n))%n,(b*pow(den,-1,n))%n) for a,b in pairs(frame['matrix'])]
        fi=[((a*den*pow(norm,-1,n))%n,(b*den*pow(norm,-1,n))%n) for a,b in pairs(frame['dual'])]
        assert pairs(r['frame'])==f and pairs(r['frame_inverse'])==fi and mm(fi,f)==eye
        if current is None:
            assert r['initial'];current=base=f;inv=fi
            origin=[(a%n,b%n) for a,b in pairs(data['before'])]
        else:
            assert not r['initial']
            base=mm(mm(f,base),fi);current=mm(mm(f,current),fi);inv=mm(mm(f,inv),fi);origin=mv(f,origin)
        assert pairs(r['base'])==base and pairs(r['origin'])==origin
        assert pairs(r['prior'])==current and pairs(r['prior_inverse'])==inv
        assert int(r['exponent_before'])==exponent and r['bound_before']==bound
        emitted=None
        for c in r['crossings']:
            depth=c['depth']
            assert bound<depth<=r['bound'] and all(prime_power(k) is None for k in range(bound+1,depth))
            p=prime_power(depth);assert p==c['prime'];bound=depth
            current=power(current,p);inv=power(inv,p);exponent*=p
            state=mv(current,origin);defect=[((a-c)%n,(b-d)%n) for (a,b),(c,d) in zip(state,origin)]
            assert pairs(c['state'])==state and pairs(c['defect'])==defect and int(c['exponent'])==exponent
            gs=[gcd(v,n) for z in defect for v in z];common=n
            for z in defect:
                for v in z:common=gcd(common,v)
            norm_defect=sum(a*a+b*b for a,b in defect)%n
            assert list(map(int,c['component_gcds']))==gs and int(c['joint_return_gcd'])==common
            assert int(c['defect_norm'])==norm_defect and int(c['norm_gcd'])==gcd(norm_defect,n)
            for d in gs+[gcd(norm_defect,n)]:
                if emitted is None and 1<d<n:emitted=d
            crossings+=1
        assert all(prime_power(k) is None for k in range(bound+1,r['bound']+1));bound=r['bound']
        assert int(r['exponent'])==exponent and pairs(r['current'])==current and pairs(r['current_inverse'])==inv
        state=mv(current,origin)
        assert pairs(r['state'])==state and pairs(r['recovered'])==mv(inv,state)==origin and mm(inv,current)==eye
        assert r['divisor']==(str(emitted) if emitted is not None else None)
        if emitted is not None:assert n%emitted==0 and emitted*(n//emitted)==n
        fields={f['name']:int(f['word']['numeral']) for f in operation['learning_context']['fields'] if f['word'].get('numeral') is not None}
        assert fields['return_exponent']==exponent and fields['return_bound']==bound
        for i,(a,b) in enumerate(state):assert fields[f'return_re_{i}']==a and fields[f'return_im_{i}']==b
    return {'source_ring_return_verified':True,'source_ring_return_actions':count,'source_ring_return_crossings':crossings}
