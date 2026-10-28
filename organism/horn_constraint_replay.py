"""Independent integer replay of the resident horn domain contraction."""
from functools import lru_cache
from math import isqrt

def extrema(d, lo, hi):
    hi=min(hi,(1<<len(d))-1)
    if lo>hi:return None
    @lru_cache(None)
    def walk(i, lower, upper):
        if i<0:return (0,0)
        lb=(lo>>i)&1;ub=(hi>>i)&1;out=[]
        for bit in (0,1):
            if d[i]!=-1 and d[i]!=bit:continue
            if lower and bit<lb or upper and bit>ub:continue
            rest=walk(i-1,lower and bit==lb,upper and bit==ub)
            if rest is not None:out.extend(((bit<<i)+rest[0],(bit<<i)+rest[1]))
        return (min(out),max(out)) if out else None
    return walk(len(d)-1,True,True)

def residue_basis(n,bits):
    modulus=1<<bits;mask=modulus-1;squares=[[] for _ in range(modulus)]
    for v in range(modulus):squares[v*v&mask].append(v)
    return [(u,v,(u-v)&mask,(u+v)&mask) for u in range(modulus) for v in squares[(u*u-n)&mask]]

def contract(n,d,basis=None,bits=0):
    ranges=[(sum((v==1)<<i for i,v in enumerate(row)),
             sum((v!=0)<<i for i,v in enumerate(row))) for row in d]
    def ceilroot(x):
        r=isqrt(x);return r+(r*r<x)
    def tighten(i,lo,hi):
        r=extrema(d[i],max(lo,ranges[i][0]),min(hi,ranges[i][1]))
        if r is None:raise ValueError('empty horn domain')
        first_difference=(r[0]^r[1]).bit_length();changed=False
        for at in range(len(d[i])-1,first_difference-1,-1):
            if d[i][at]==-1:d[i][at]=(r[0]>>at)&1;changed=True
        ranges[i]=r;return changed
    try:
        while True:
            changed=False
            if basis is not None:
                supports=[[0]*bits for _ in range(4)];count=0
                for row in basis:
                    if not all(all((d[lane][i] if i<len(d[lane]) else 0) in (-1,(row[lane]>>i)&1) for i in range(bits)) for lane in range(4)):continue
                    count+=1
                    for lane in range(4):
                        for i in range(bits):supports[lane][i]|=1<<((row[lane]>>i)&1)
                if not count:return False
                for lane in range(4):
                    for i in range(min(bits,len(d[lane]))):
                        if d[lane][i]==-1 and supports[lane][i] in (1,2):
                            d[lane][i]=supports[lane][i]-1;changed=True
            changed=tighten(0,ceilroot(n+ranges[1][0]**2),isqrt(n+ranges[1][1]**2)) or changed
            if ranges[0][1]**2<n:return False
            changed=tighten(1,ceilroot(max(0,ranges[0][0]**2-n)),isqrt(ranges[0][1]**2-n)) or changed
            changed=tighten(0,(ranges[2][0]+ranges[3][0]+1)//2,(ranges[2][1]+ranges[3][1])//2) or changed
            if ranges[3][1]<ranges[2][0]:return False
            changed=tighten(1,(max(0,ranges[3][0]-ranges[2][1])+1)//2,(ranges[3][1]-ranges[2][0])//2) or changed
            if ranges[0][1]<ranges[1][0]:return False
            changed=tighten(2,max(3,ranges[0][0]-ranges[1][1]),ranges[0][1]-ranges[1][0]) or changed
            changed=tighten(3,ranges[0][0]+ranges[1][0],ranges[0][1]+ranges[1][1]) or changed
            if not changed:return True
    except ValueError:return False

def verify(task,n):
    h=task.get('toroidal_division',{}).get('horn_contraction')
    if h is None:return {}
    assert h['schema'] in ('resident-zero-horn-contraction-v1','resident-zero-horn-contraction-v2') and int(h['source'])==n
    bits=h.get('joint_residue_bits',0);basis=residue_basis(n,bits) if bits else None
    if bits:
        assert bits==min(12,n.bit_length())
        assert h['joint_residue_rows']==(len(basis) if h['calls'] else 0)
    assert h['coordinate_order']==['u','v','p','q'] and h['calls']==len(h['receipts'])
    forced=rejected=probed=0
    for index,row in enumerate(h['receipts']):
        before=row['before'];d=[x[:] for x in before]
        assert len(d)==4 and all(v in (-1,0,1) for lane in d for v in lane)
        supported=contract(n,d,basis,bits)
        probe=row['probe']
        if supported:
            free=[(i,j) for i,lane in enumerate(d) for j in range(len(lane)-1,-1,-1) if lane[j]==-1]
            if free:
                probed+=1;i,j=free[index%len(free)]
                assert (probe['coordinate'],probe['position'])==(i,j)
                admitted=[]
                for bit in (0,1):
                    trial=[x[:] for x in d];trial[i][j]=bit;admitted.append(contract(n,trial,basis,bits))
                assert admitted==probe['admitted']
                if not any(admitted):supported=False
                elif not all(admitted):d[i][j]=admitted.index(True)
                if supported:supported=contract(n,d,basis,bits)
            else:assert probe is None
        else:assert probe is None
        assert row['after']==d and row['rejected']==(not supported)
        assert row['branch_preserving']
        rejected+=not supported
        if supported:forced+=sum(a==-1 and b!=-1 for x,y in zip(before,d) for a,b in zip(x,y))
    return dict(horn_contraction_verified=True,horn_contraction_calls=h['calls'],
                horn_contraction_probes=probed,horn_contraction_forced=forced,horn_contraction_rejected=rejected)
