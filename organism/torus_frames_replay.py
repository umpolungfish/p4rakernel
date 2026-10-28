"""Independent source-ring replay of the executing carried frame and readout."""
from math import gcd


def verify(data, context, n):
    r=data['carried_torus_frame']
    fields={f['name']:f['word'] for f in context['fields']}
    raw_p,raw_q=(int(fields[k]['numeral']) for k in ('p','q'))
    height_frame=r['schema'] in ('carried-source-height-torus-frame-v2','carried-source-height-torus-frame-v3')
    p,q=raw_p%n,raw_q%n
    if height_frame:
        height=int(fields['height']['numeral']);negative=int(fields['negative']['numeral'])
        assert negative in (0,1)
        assert raw_p*raw_q==n+(-1 if negative else 1)*height*(1<<n.bit_length())
        assert list(map(int,r['input_pair']))==[raw_p,raw_q]
        assert int(r['height'])==height and r['height_negative']==bool(negative)
        assert r['source_relation_verified']
        q=(-height if negative else height)%n
    assert int(r['source'])==n and list(map(int,r['parameters']))==[p,q]
    assert r['source_bank_retained']
    def circle(t):
        den=(1+t*t)%n
        return ((1-t*t)*pow(den,-1,n)%n,2*t*pow(den,-1,n)%n)
    if r['stage']=='coordinate-nonunit':
        which={'azimuth-parameter':p,'tube-parameter':q,'height-parameter':q}[r['coordinate']]
        d=gcd(1+which*which,n)
        assert d!=1 and int(r['gcd'])==d and r['held']==(not 1<d<n)
        return p,q,(d if 1<d<n else None)
    assert r['stage']=='frame-return'
    tube=circle(q)
    if height_frame:tube=(-tube[0]%n,tube[1])
    before=[circle(p),tube]
    if height_frame:
        ca,sa=before[0];cb,sb=before[1]
        source_horn=[ca*(1+cb)%n,sa*(1+cb)%n,sb]
        assert list(map(int,r['source_horn']))==source_horn
        assert r['exact_height_zero']==(height==0)
        if height==0:assert source_horn==[0,0,0]
    assert [tuple(map(int,x)) for x in r['before']]==before
    def mul(x,y):
        a,b=x;c,d=y
        return ((a*c-b*d)%n,(a*d+b*c)%n)
    def power(x,k):
        if k<0:x=(x[0],-x[1]%n);k=-k
        out=(1,0)
        while k:
            if k&1:out=mul(out,x)
            x=mul(x,x);k//=2
        return out
    def wind(z,m):return [mul(power(z[0],a),power(z[1],b)) for a,b in m]
    matrix=[[-47,256],[-9,49]] if r['tick']%2==0 else [[-38,169],[-9,40]]
    assert r['matrix']==matrix
    (a,b),(c,d)=matrix
    inverse=[[d,-b],[-c,a]]
    assert r['inverse_matrix']==inverse and a*d-b*c==1
    after=wind(before,matrix)
    assert [tuple(map(int,x)) for x in r['after']]==after
    assert [tuple(map(int,x)) for x in r['recovered']]==wind(after,inverse)==before
    assert all((a*a+b*b)%n==1 for a,b in after) and r['inverse_verified']
    ca,sa=after[0];cb,sb=after[1]
    normal=[ca*cb%n,sa*cb%n,sb]
    candidates=[];readout=None
    for frame,(name,R,minor) in zip(r['frames'],[('horn',1,1),('spindle',1,2),('open',2,1)]):
        assert (frame['name'],frame['R'],frame['r'])==(name,R,minor)
        centre=[R*ca%n,R*sa%n,0]
        outer=[(c+minor*v)%n for c,v in zip(centre,normal)]
        inner=[(c+R*v)%n for c,v in zip(centre,normal)]
        for key,value in [('normal',normal),('centreline',centre),('outer',outer),('miniature',inner)]:
            assert list(map(int,frame[key]))==value
        assert [(o-minor*v)%n for o,v in zip(outer,normal)]==centre
        assert [(o-i)%n for o,i in zip(outer,inner)]==[(minor-R)*v%n for v in normal]
        radial=(R+minor*cb)%n;g=gcd(radial,n)
        assert int(frame['signed_radius'])==radial and int(frame['radial_gcd'])==g
        assert frame['normal_return_verified']
        if 1<g<n:candidates.append(g)
        if name=='spindle':
            azimuth=tuple(centre[:2]);tube=((normal[0]*azimuth[0]+normal[1]*azimuth[1])%n,normal[2])
            readout=[azimuth,tube]
    assert readout==after==[tuple(map(int,x)) for x in r['normal_readout']]
    if r['schema']=='carried-source-height-torus-frame-v3':
        split=r['sphere_split'];direction=[ca,sa,0]
        plus=[(a+b)%n for a,b in zip(normal,direction)]
        minus=[(a-b)%n for a,b in zip(normal,direction)]
        half=pow(2,-1,n)
        fused_normal=[(a+b)*half%n for a,b in zip(plus,minus)]
        fused_direction=[(a-b)*half%n for a,b in zip(plus,minus)]
        for key,expected in [('outer',[2*a%n for a in normal]),
                ('inner_plus',plus),('inner_minus',minus),
                ('fused_normal',fused_normal),('fused_direction',fused_direction)]:
            assert list(map(int,split[key]))==expected
        assert sum(a*b for a,b in zip(plus,minus))%n==0
        assert fused_normal==normal and fused_direction==direction
        assert [tuple(map(int,x)) for x in split['readout']]==readout
        assert split['source_lifts_retained']
    parameters=[]
    for i,((c,s),seam) in enumerate(zip(readout,r['chart_seams'])):
        den=(1-c if height_frame and i==1 else 1+c)%n;g=gcd(den,n)
        assert seam['coordinate']==i and int(seam['denominator'])==den and int(seam['gcd'])==g
        assert seam['held']==(g!=1)
        if g==1:parameters.append(s*pow(den,-1,n)%n)
        else:
            parameters.append([p,q][i])
            if 1<g<n:candidates.append(g)
    assert list(map(int,r['readout_parameters']))==parameters
    emitted=candidates[0] if candidates else None
    assert r['divisor']==(str(emitted) if emitted is not None else None)
    return *parameters,emitted
