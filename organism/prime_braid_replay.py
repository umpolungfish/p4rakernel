"""Replay source path addresses, contraction and the executed joint phases."""
from fractions import Fraction
from mpmath import mp

def verify(data, context, n, bits):
    braid=data['prime_braid']
    fields={f['name']:int(f['word']['numeral']) for f in context['fields'] if f['name'] in ('p','q','clock')}
    assert braid['schema']=='source-square-wave-joint-braid-v1'
    assert int(braid['source'])==n and int(braid['clock'])==fields['clock']
    assert braid['well_order']==['p','q']
    assert braid['channel_order']==['p-positive','p-negative','q-positive','q-negative']
    scale=1<<bits;roots=[]
    vector=lambda v:tuple(map(int,v))
    def rounded(v):return (-1 if v<0 else 1)*((abs(v)+scale//2)//scale)
    def product(z,w):
        a,b=z;c,d=w
        return rounded(a*c-b*d),rounded(a*d+b*c)
    with mp.workprec(bits+100):
        for row,label,partner in zip(braid['paths'],(fields['p'],fields['q']),(fields['q'],fields['p'])):
            ordinal=partner+fields['clock'];segment,sample=divmod(ordinal,30);quadrant=segment%4
            assert int(row['label'])==label and row['label_status']=='unverified-factor-alternative'
            assert int(row['segments'])==4*label and int(row['samples'])==120*label
            assert (int(row['ordinal']),int(row['segment']),row['sample'],row['quadrant'])==(ordinal,segment,sample,quadrant)
            assert int(row['completed_paths'])==ordinal//(120*label)
            levels=[11,0,-11,0]
            if sample<20:
                azimuth=Fraction(segment*19+sample,label*76);tube=Fraction(levels[quadrant],40);drift=Fraction(0)
            else:
                j=sample-20;azimuth=Fraction(segment+1,label*4)
                tube=Fraction(levels[quadrant]*(9-j)+levels[(quadrant+1)%4]*j,360);drift=Fraction(j,450)
            assert Fraction(*map(int,row['azimuth_turns']))==azimuth
            assert Fraction(*map(int,row['tube_turns']))==tube
            assert Fraction(*map(int,row['connector_radians']))==drift
            a,b=vector(row['azimuth_root']),vector(row['tube_root'])
            angles=[2*mp.pi*mp.mpf(azimuth.numerator)/azimuth.denominator+mp.mpf(drift.numerator)/drift.denominator,
                    2*mp.pi*mp.mpf(tube.numerator)/tube.denominator]
            for z,angle in zip((a,b),angles):
                assert abs(z[0]-int(mp.nint(scale*mp.cos(angle))))<=3
                assert abs(z[1]-int(mp.nint(scale*mp.sin(angle))))<=3
            direction=(a[0]*scale,a[1]*scale,0);normal=(a[0]*b[0],a[1]*b[0],b[1]*scale)
            plus=tuple(x+y for x,y in zip(normal,direction));minus=tuple(x-y for x,y in zip(normal,direction))
            assert vector(row['sphere_inner_plus'])==plus and vector(row['sphere_inner_minus'])==minus
            assert vector(row['returned_direction'])==direction and vector(row['returned_normal'])==normal
            assert int(row['spatial_denominator'])==scale*scale
            for frame,(name,r) in zip(row['frames'],(('horn',2),('spindle',1),('sphere',0))):
                assert frame['name']==name and frame['R']==r and frame['r']==2
                assert vector(frame['outer'])==tuple(r*x+2*y for x,y in zip(direction,normal))
                assert vector(frame['original_inner'])==tuple(r*(x+y) for x,y in zip(direction,normal))
            assert row['inner_return_verified'] and row['phase_input_from_inner_return']
            pair=[product(a,b),product(a,(b[0],-b[1]))]
            assert [vector(z) for z in row['roots']]==pair
            roots.extend(pair)
    assert [vector(z) for z in braid['roots']]==roots
    return roots
