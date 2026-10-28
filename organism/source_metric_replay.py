"""Replay the source metric and signed inner copies through the native operator."""
from math import gcd


def verify(data, context, n, projectors):
    metric=data['source_metric']
    fields={f['name']:int(f['word']['numeral']) for f in context['fields']
            if f['name'] in ('p','q','height','negative','clock')}
    p,q=fields['p'],fields['q'];period=1<<n.bit_length()
    height=(-1 if fields['negative'] else 1)*fields['height']
    assert p*q==n+height*period
    vector=lambda rows:[tuple(map(int,z)) for z in rows]
    def gram(z):return [(a*c+b*d,a*d-b*c) for a,b in z for c,d in z]
    def product(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def action(matrix,z):
        return [tuple(sum(product(matrix[4*i+j],z[j])[k] for j in range(4))
                      for k in range(2)) for i in range(4)]
    denominator=int(data['action_denominator'])
    matrix=vector(data['banked_frame']['matrix'])
    dual=vector(data['banked_frame']['dual'])
    normalization=int(data['banked_frame']['dual_normalization'][0])
    readouts=[];candidate=None
    assert len(metric['branches'])==2
    for row,(name,lift,h) in zip(metric['branches'],[
            ('positive',q,height),('complementary',q-period,height-p)]):
        assert row['lift']==name
        assert [int(row[k]) for k in ['source','p','q','height','period']]==[n,p,lift,h,period]
        u,v=(p+lift)//2,(p-lift)//2
        assert [int(row[k]) for k in ['u','v','major_squared','minor_squared','product_defect']]==[
            u,v,u*u,v*v+n,p*lift-n]
        assert u*u-(v*v+n)==h*period
        source=[(p,0),(1,0),(lift,0),(-1,0)]
        inner=[(u,0),(0,0),(v,0),(1,0)]
        assert vector(row['source_amplitudes'])==source
        assert vector(row['inner_amplitudes'])==inner
        assert vector(row['source_gram'])==gram(source)
        assert row['split_fuse_verified'] and row['source_context_retained']
        bank=row['banked_frame']
        for key in ['matrix','dual','dual_normalization','addresses','wires']:
            assert bank[key]==data['banked_frame'][key]
        anchor=bank['frame']['anchored_return']
        assert bank['frame']['edges']==data['banked_frame']['frame']['edges']
        assert bank['frame']['nodes']==data['banked_frame']['frame']['nodes']
        assert anchor['source_start']==2*n.bit_length() and anchor['source_width']==n.bit_length()
        assert int(anchor['source'])==n and anchor['source_preserved']
        assert anchor['same_arena'] and anchor['output_before_fixation'] and bank['output_port_consumed']
        after=action(matrix,inner)
        assert vector(bank['exact_output'])==after
        assert action(dual,after)==[(a*normalization,b*normalization) for a,b in inner]
        fused=[tuple(after[a][k]+sign*after[b][k] for k in range(2))
               for a,b,sign in [(0,2,1),(1,3,1),(0,2,-1),(1,3,-1)]]
        returned=row['return'];assert vector(returned['inner_after'])==after
        assert vector(returned['fused_after'])==fused
        assert int(returned['amplitude_denominator'])==denominator
        observed=gram(fused)
        assert vector(returned['gram'])==observed
        defect=tuple(observed[2][k]+n*observed[7][k] for k in range(2))
        assert tuple(map(int,returned['weighted_product_gram']))==defect
        assert int(returned['gram_denominator'])==denominator**2
        masses=[sum(a*c+b*d for (a,b),(c,d) in zip(projector,observed))
                for projector in projectors]
        assert list(map(int,returned['mass_numerators']))==masses
        dual_den=int(returned['dual_denominator']);assert dual_den>0
        assert vector(returned['dual_numerators'])==[(a*dual_den,b*dual_den) for a,b in observed]
        values=[value for z in fused for value in z]+list(defect)
        divisors=[gcd(value,n) for value in values]
        assert list(map(int,returned['coordinate_gcds']))==divisors
        for d in divisors:
            if 1<d<n and candidate is None:candidate=d
        assert returned['exact_sic_return']
        readouts.append(fused[0][0]*pow(denominator,-1,n)%n)
    selected=fields['clock']%2
    assert metric['rotation_branch']==selected and metric['input_context_retained']
    assert int(metric['rotation_readout'])==readouts[selected]
    assert int(data['source_metric_rotation_readout'])==readouts[selected]
    assert metric['divisor']==(None if candidate is None else str(candidate))
    if data.get('source_divisor_origin')=='source-metric-inner-return':
        assert candidate==int(data['source_divisor']['numeral'])
    return candidate
