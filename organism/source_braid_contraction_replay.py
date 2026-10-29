"""Independent exact replay of native coefficient tasks and retained source graph."""
import hashlib,json,mmap,struct
from array import array
from pathlib import Path

def numeral(word):
    assert word.startswith('⊢') and word.endswith('⊙⊡⊣')
    if word=='⊢⊙⊡⊣':return 0
    cells=word[1:-3];assert len(cells)%5==0
    result=0
    for i in range(len(cells)//5):
        c=cells[5*i:5*i+5];assert c[:3]=='≻⋈∈' and c[4]=='∋' and c[3] in '⊤⊥'
        if c[3]=='⊥':result|=1<<i
    assert result and cells[-2]=='⊥'
    return result

def audit_binary(image):
    import subprocess
    image=Path(image)
    symbols=subprocess.run(['nm','-C',str(image)],capture_output=True,text=True,check=True).stdout.splitlines()
    patterns=['factor_synthesis::','glut_fold::','glut_correlation::','mpqs','pollard','brent','gpu_ecm::']
    counts={p:sum(p in line.lower() for line in symbols) for p in patterns}
    count=sum('source_braid_contraction::' in line for line in symbols)
    assert count and not any(counts.values())
    return dict(kind='compiled-symbol-scope',image=str(image),sha256=hashlib.sha256(image.read_bytes()).hexdigest(),
                source_contraction_symbols=count,forbidden_pattern_counts=counts)

def verify_context(event,tokens,n):
    context=event['learning_context'];assert context['schema']=='source-braid-learning-context-v1'
    assert tokens[:3]==[256,85,context['arm']] and context['arm']==event['port']%3
    expected={'source':n,'factor':event['factor'],'root':event['root'],'nodes':event['nodes'],
              'eliminated':event['eliminated'],'reentry_mask':event['reentry_state'],
              'negative_chart':int(event['negative_chart'])}
    assert [f['name'] for f in context['fields']]==list(expected)
    at=3
    for i,field in enumerate(context['fields']):
        assert tokens[at]==i;at+=1;width=int.from_bytes(bytes(tokens[at:at+8]),'little');at+=8
        cells=[]
        for _ in range((width+1)//2):
            packed=tokens[at]-266;at+=1;assert 0<=packed<16
            cells.extend(['N','T','F','B'][(packed>>j)&3] for j in (0,2))
        cells=cells[:width];assert all(c in ('T','F') for c in cells)
        assert cells==field['word']['cells']
        value=sum((c=='T')<<j for j,c in enumerate(cells))
        assert value==int(field['word']['numeral'])==expected[field['name']]
    assert tokens[at:]==[257]

def verify(task,n):
    assert task['schema']=='source-braid-contraction-v1' and task['construction']=='source-braid-contraction'
    assert task['error'] is None,task['error']
    assert numeral(task['source_word'])==n and int(task['source'])==n and n.bit_length()>=2
    prep=task['preparation'];assert prep['source_bits']==n.bit_length() and numeral(prep['source_word'])==n
    assert prep['numeral_arithmetic']=='WordTape/SignedWordTape' and prep['residue_pairs_enumerated']==0
    sic=prep['sic'];rays=[[(int(a),int(b)) for a,b in row] for row in sic['rays']]
    def gram(z):return [(a*c+b*d,a*d-b*c) for a,b in z for c,d in z]
    projectors=[gram(ray) for ray in rays];recovered=[]
    assert len(sic['basis'])==16
    for record in sic['basis']:
        g=[tuple(map(int,x)) for x in record['input']]
        masses=[sum(a*c+b*d for (a,b),(c,d) in zip(P,g)) for P in projectors]
        assert masses==list(map(int,record['masses']))
        den=int(record['denominator']);back=[tuple(map(int,x)) for x in record['numerators']]
        assert den>0 and back==[(a*den,b*den) for a,b in g]
        recovered.append((back,den))
    for a in range(4):
        for b in range(4):
            u,du=recovered[a];v,dv=recovered[b]
            value=sum(u[4*i+j][0]*v[4*j+i][0]-u[4*i+j][1]*v[4*j+i][1] for i in range(4) for j in range(4))
            assert value in (0,du*dv)
            assert sic['kernel'][a][b]==(value==du*dv)==(a==b)
    assert sic['address_rule']=={'ordinal':'120*x','azimuth_turns':'x/N','tube_turns':[11,40],'square_return':'120*(x*x mod N)'}
    inner=sic['inner_return'];assert inner['plus']==['1','1'] and inner['minus']==['-1','1']
    assert [(numeral(c['word'])*(-1 if c['negative'] else 1)) for c in inner['returned']]==[1,0]

    circuit_path=Path(prep['circuit']);circuit_file=circuit_path.open('rb');data=mmap.mmap(circuit_file.fileno(),0,access=mmap.ACCESS_READ)
    assert data[:4]==b'BSC1';bits,variables,gate_count,output=struct.unpack_from('<QQQQ',data,4)
    assert bits==n.bit_length() and variables==2*bits+gate_count
    assert gate_count==prep['nand_gates'] and variables==prep['variables'] and output==prep['output']
    assert len(data)==36+24*gate_count
    last=array('Q',[0])*variables
    x=n//7+19
    cases=[(n//3+17,n//5+11),(x,x),(x,n-x),(n,n//13+29)]
    mask=(1<<len(cases))-1;values=bytearray(variables)
    for i in range(bits):
        values[i]=sum(((a>>i)&1)<<j for j,(a,b) in enumerate(cases))
        values[bits+i]=sum(((b>>i)&1)<<j for j,(a,b) in enumerate(cases))
    def read(w):return values[w-2] if w>=2 else mask*w
    for index in range(gate_count):
        a,b,z=struct.unpack_from('<QQQ',data,36+24*index)
        assert z==2*bits+index and a<z+2 and b<z+2
        for w in (a,b,z+2):
            if w>=2:last[w-2]=index
        values[z]=mask^(read(a)&read(b))
    if output>=2:last[output-2]=gate_count
    got=read(output)
    for j,(a,b) in enumerate(cases):assert bool(got&(1<<j))==(a<n and b<n and a*a%n==b*b%n)

    retained_path=Path(task['retained_state']['path']);raw=retained_path.read_bytes()
    assert len(raw)==task['retained_state']['bytes']
    state=json.loads(raw);assert numeral(state['source_word'])==n
    arena=state['arena'];nodes=arena['nodes'];keys={};heads=[];coefficients={}
    for i,node in enumerate(nodes):
        kind=node[0]
        if kind=='zero':assert i==0;key=('zero',);head=variables
        elif kind=='coefficient':
            value=numeral(node[2])*(-1 if node[1] else 1);assert value
            coefficients[i]=value;key=('coefficient',value);head=variables
        else:
            assert kind=='branch';_,wire,lo,hi=node
            assert 0<=wire<variables and 0<=lo<i and 0<hi<i
            assert heads[lo]>wire and heads[hi]>wire
            key=('branch',wire,lo,hi);head=wire
        assert key not in keys;keys[key]=i;heads.append(head)
    def leaf(c):return 0 if c==0 else keys[('coefficient',c)]
    def branch(w,lo,hi):return lo if hi==0 else keys[('branch',w,lo,hi)]
    cache={tuple(op):r for op,r in arena['cache']};assert len(cache)==len(arena['cache'])
    def add(a,b):return ('add',min(a,b),max(a,b))
    def parts(a,w):return (nodes[a][2],nodes[a][3]) if heads[a]==w else (a,0)
    dependencies={}
    for op,result in cache.items():
        kind=op[0];deps=[]
        def get(key):deps.append(key);return cache[key]
        if kind=='add':
            _,a,b=op;assert 0<=a<=b<len(nodes)
            if a==0:expected=b
            elif a in coefficients and b in coefficients:expected=leaf(coefficients[a]+coefficients[b])
            else:
                w=min(heads[a],heads[b]);al,ah=parts(a,w);bl,bh=parts(b,w)
                expected=branch(w,get(add(al,bl)),get(add(ah,bh)))
        elif kind in ('neg','double'):
            _,a=op
            if a==0:expected=0
            elif a in coefficients:expected=leaf(coefficients[a]*(-1 if kind=='neg' else 2))
            else:_,w,lo,hi=nodes[a];expected=branch(w,get((kind,lo)),get((kind,hi)))
        else:
            assert kind in ('force','eliminate');_,w,a=op;assert 0<=w<variables and 0<=a<len(nodes)
            if a==0:expected=0
            elif heads[a]<w:
                _,v,lo,hi=nodes[a];expected=branch(v,get((kind,w,lo)),get((kind,w,hi)))
            elif heads[a]==w:
                _,v,lo,hi=nodes[a]
                if kind=='force':expected=branch(w,0,get(add(lo,hi)))
                else:expected=get(add(get(('double',lo)),hi))
            elif kind=='force':expected=branch(w,0,a)
            else:expected=get(('double',a))
        assert result==expected,(op,result,expected)
        dependencies[op]=deps
    colors={}
    for root in cache:
        stack=[(root,False)]
        while stack:
            key,done=stack.pop()
            if done:colors[key]=2;continue
            if colors.get(key)==2:continue
            assert colors.get(key)!=1,'cyclic coefficient proof'
            colors[key]=1;stack.append((key,True));stack.extend((d,False) for d in dependencies[key] if colors.get(d)!=2)

    def prefix(kind,factor):
        instructions=[]
        def push(i):slot=2+len(instructions);instructions.append(i);return slot
        def monomial(ws):
            if any(w==0 for w in ws):return 1
            slot=0
            for w in sorted({w-2 for w in ws if w>=2}):slot=push(['force',slot,w])
            return slot
        if kind=='chart-involution':push(['neg',0]);return instructions
        assert kind=='source-factor' and factor<=gate_count
        if factor<gate_count:
            a,b,z=struct.unpack_from('<QQQ',data,36+24*factor)
            xy=monomial([a,b]);zz=monomial([z+2]);xyz=monomial([a,b,z+2])
            sum_slot=push(['add',xy,zz]);twice=push(['double',xyz]);negative=push(['neg',twice]);out=push(['add',sum_slot,negative])
        else:out=monomial([output])
        push(['add',out,1]);return instructions
    eliminated=[]
    def plan(p,complete):
        ins=p['instructions'];pre=prefix(p['kind'],p['factor']);assert ins[:len(pre)]==pre
        previous=2+len(pre)-1
        if p['kind']=='chart-involution':assert len(ins)==len(pre)
        else:
            wires=[]
            for index,i in enumerate(ins[len(pre):],len(pre)):
                assert i[0]=='eliminate' and i[1]==previous and last[i[2]]==p['factor']
                wires.append(i[2]);previous=2+index
            assert wires==sorted(set(wires))
            if complete:eliminated.extend((p['factor'],w) for w in wires)
        cursor=p['cursor'];slots=p['slots'];assert len(slots)==2+cursor and slots[:2]==[p['before'],0]
        assert len(p['steps'])==cursor
        for j,i in enumerate(ins[:cursor]):
            if i[0]=='add':op=add(slots[i[1]],slots[i[2]])
            elif i[0] in ('force','eliminate'):op=(i[0],i[2],slots[i[1]])
            else:op=(i[0],slots[i[1]])
            assert p['steps'][j]==[list(op),cache[op]] and slots[j+2]==cache[op]
        if complete:assert cursor==len(ins) and p['after']==slots[-1]
    root=1;factor=0;negative=False
    for bank in state['banks']:
        assert bank['before']==root and bank['factor']==factor;plan(bank,True);root=bank['after']
        if bank['kind']=='chart-involution':negative=not negative
        else:factor+=1
    assert root==state['root'] and factor==state['factor']==task['factor_cursor'] and negative==state['negative_chart']
    assert eliminated==sorted(set(eliminated)) and len(eliminated)==state['elimination_cursor']==task['eliminated_variables']
    assert len(eliminated)==sum(last_use<factor for last_use in last)
    if state['pending_plan'] is not None:
        pending=state['pending_plan'];assert pending['before']==root and pending['factor']==factor;plan(pending,False)
    mask_state=0
    for e in task['logical_reentry']:
        a,b,c,k=e['before'],e['permuted'],e['after'],e['kind'];assert a==mask_state
        assert b==((a&1)<<1)|((a&2)>>1)|((a&4)<<1)|((a&8)>>1)
        expected=15^(((a&1)<<3)|((a&2)<<1)|((a&4)>>1)|((a&8)>>3)) if k==2 else next((a|bit for bit in (1,2,4,8) if not a&bit),a)
        assert k in (1,2) and (k==2)==(a==15) and c==expected;mask_state=c
    assert state['requested_negative_chart']==bool(mask_state&4)
    result=task.get('result')
    if result:
        assert factor==gate_count+1 and len(eliminated)==variables and root in coefficients
        count=coefficients[root]*(-1 if negative else 1);assert numeral(result['collision_count_word'])==count
        tau=(4*n-count-3)//4;assert 4*tau==4*n-count-3 and numeral(result['tau_word'])==tau
        p,q=int(result['p']),int(result['q']);assert 1<p<n and n%p==0 and n//p==q and p*q==n
        assert numeral(result['p_word'])==p and numeral(result['q_word'])==q
        assert result['exact_product'] and result['paired_boundary']
    report=dict(source_contraction_replay_passed=True,source_circuit_probe_count=len(cases),
        source_circuit_gates=gate_count,source_circuit_variables=variables,coefficient_nodes=len(nodes),
        exact_coefficient_tasks=len(cache),committed_factors=factor,eliminated_variables=len(eliminated),
        retained_continuation_verified=True,source_sic_basis_returns=len(recovered),
        source_circuit_sha256=hashlib.sha256(data).hexdigest(),retained_state_sha256=hashlib.sha256(raw).hexdigest())
    data.close();circuit_file.close();return report
