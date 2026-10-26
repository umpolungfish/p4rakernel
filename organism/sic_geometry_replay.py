"""Independent integer replay of the organism's full-complex SIC rotation."""
from mpmath import mp

def verify(task, n):
    preparation=task.get('sic_geometry_preparation')
    if preparation is None:return {}
    def vector(rows):return [tuple(map(int,z)) for z in rows]
    def gram(z):
        return [(a*c+b*d,a*d-b*c) for a,b in z for c,d in z]
    bits=preparation['fractional_bits'];scale=1<<bits
    rays=[vector(ray) for ray in preparation['rays']]
    projectors=[gram(ray) for ray in rays]
    state=vector(preparation['amplitudes'])
    count=changed=0;maximum_inverse=0
    for operation in task['operations']:
        event=operation['toroidal_operation']
        data=event.get('geometric_sic')
        if data is None:continue
        count+=1;assert data['tick']==count
        assert vector(data['before'])==state
        context=data['input_context'];fields={f['name']:f['word'] for f in context['fields']}
        def numeral(name):return int(fields[name]['numeral'])
        assert numeral('source')==n
        width=n.bit_length();denominator=1<<(2*((width+1)//2))
        turns=numeral('positive_turns')-numeral('negative_turns')
        numerator=(numeral('p')-numeral('q')+turns)%denominator
        assert int(data['winding_numerator'])==numerator
        assert int(data['winding_denominator'])==denominator
        assert int(data['signed_turns'])==turns
        assert data['fourier_inverse']==bool(numeral('clock')%2)
        coefficients=vector(data['winding_coefficients'])
        with mp.workprec(bits+80):
            for k,(re,im) in enumerate(coefficients):
                angle=-2*mp.pi*((numerator*k)%denominator)/denominator
                assert abs(re-int(mp.nint(scale*mp.cos(angle))))<=2
                assert abs(im-int(mp.nint(scale*mp.sin(angle))))<=2
        def rounded(value):
            return (-1 if value<0 else 1)*((abs(value)+(scale>>1))//scale)
        phase_state=state
        if 'source_fibre' in data:
            fibre=data['source_fibre'];assert fibre==context['source_fibre']
            assert fibre['enclosure']=='B'
            level=3+numeral('clock')%(width-3);assert fibre['level']==level
            mask=(1<<(level+1))-1;lowmask=(1<<level)-1
            assert int(fibre['source']['numeral'])==n&mask
            for name,origin in [('p_alternatives',numeral('p')),('q_alternatives',numeral('q'))]:
                cells=fibre[name]['cells'];assert cells[level]=='B'
                assert all(cell in ('T','F') for cell in cells[:level])
                assert sum((cell=='T')<<i for i,cell in enumerate(cells[:level]))==origin&lowmask
            signs=[]
            for label,row in enumerate(fibre['rows']):
                assert row['label']==label
                left=(numeral('p')&lowmask)|((label//2)<<level)
                right=(numeral('q')&lowmask)|((label%2)<<level)
                assert int(row['p']['numeral'])==left and int(row['q']['numeral'])==right
                product=left*right&mask;assert int(row['product']['numeral'])==product
                admitted=product==(n&mask);assert row['evidence']==('T' if admitted else 'F')
                signs.append(admitted)
            assert sum(signs)==2
            if 'source_phase_quarter_turns' in data:
                assert data['source_phase_quarter_turns']==1 and signs==data['source_phase_marked']
                phase_state=[(-b,a) if sign else (a,b) for (a,b),sign in zip(state,signs)]
                assert [(b,-a) if sign else (a,b) for (a,b),sign in zip(phase_state,signs)]==state
            else:
                assert signs==data['source_phase_negative']
                phase_state=[(-a,-b) if sign else (a,b) for (a,b),sign in zip(state,signs)]
                assert [(-a,-b) if sign else (a,b) for (a,b),sign in zip(phase_state,signs)]==state
            assert vector(data['source_phase_after'])==phase_state
        wound=[(rounded(a*c-b*d),rounded(a*d+b*c))
               for (a,b),(c,d) in zip(phase_state,coefficients)]
        after=[]
        for row in range(4):
            re=im=0
            for col,(a,b) in enumerate(wound):
                phase=(-row*col if data['fourier_inverse'] else row*col)%4
                x,y=[(a,b),(-b,a),(-a,-b),(b,-a)][phase]
                re+=x;im+=y
            def half(v):return (-1 if v<0 else 1)*(abs(v)//2)
            after.append((half(re),half(im)))
        assert vector(data['after'])==after
        learned={f['name']:f['word'] for f in operation['learning_context']['fields']}
        for i,(re,im) in enumerate(after):
            for name,value in [(f'sic_re_{i}',abs(re)),(f'sic_im_{i}',abs(im)),
                               (f'sic_re_negative_{i}',int(re<0)),(f'sic_im_negative_{i}',int(im<0))]:
                assert int(learned[name]['numeral'])==value
        assert int(learned['sic_tick']['numeral'])==count
        assert int(learned['sic_fractional_bits']['numeral'])==bits
        observed=gram(after);assert vector(data['gram'])==observed
        masses=[sum(a*c+b*d for (a,b),(c,d) in zip(projector,observed))
                for projector in projectors]
        assert masses==list(map(int,data['mass_numerators']))
        exact=vector(data['exact_dual_numerators']);dual_den=int(data['exact_dual_denominator'])
        assert dual_den>0 and exact==[(a*dual_den,b*dual_den) for a,b in observed]
        total=sum(masses);analytic_den=4*scale**4
        assert analytic_den==int(data['analytic_denominator'])
        residuals=[]
        for entry,(a,b) in enumerate(observed):
            re=5*sum(mass*projector[entry][0] for mass,projector in zip(masses,projectors))
            im=5*sum(mass*projector[entry][1] for mass,projector in zip(masses,projectors))
            if entry%5==0:re-=total*scale**2
            residuals.append((re-a*analytic_den,im-b*analytic_den))
        assert residuals==vector(data['analytic_signed_residuals'])
        assert int(data['analytic_residual'])<=int(data['analytic_tolerance'])
        inverse=vector(data['inverse_return'])
        inverse_residual=max(abs(a-c) for z,w in zip(state,inverse) for a,c in zip(z,w))
        assert inverse_residual==int(data['inverse_residual'])<=int(data['inverse_tolerance'])
        maximum_inverse=max(maximum_inverse,inverse_residual)
        trace=sum(exact[5*i][0] for i in range(4));imaginary=exact[1][1]
        period=1<<(width-3);lift,remainder=divmod(period*abs(imaginary),trace)
        assert int(data['orbit_period'])==period and int(data['lift'])==lift
        assert int(data['projection_remainder'])==remainder
        assert data['reverse']==(imaginary<0)
        rotation=data['rotation'];transition=rotation['transition']
        assert rotation['arm']==context['arm']==event['arm']
        assert int(transition['lift']['numeral'])==lift and transition['reverse']==data['reverse']
        previous=transition['before'];assert int(previous['p']['numeral'])==numeral('p')
        assert int(previous['q']['numeral'])==numeral('q')
        modulus=1<<width;torus=task['toroidal_division']
        step=int(torus['inverse_step' if data['reverse'] else 'step']['numeral'])
        back=int(torus['step' if data['reverse'] else 'inverse_step']['numeral'])
        assert int(transition['after_p']['numeral'])==numeral('p')*pow(step,lift,modulus)%modulus
        assert int(transition['after_q']['numeral'])==numeral('q')*pow(back,lift,modulus)%modulus
        assert data['coherence_changed']==(gram(state)!=observed)
        changed+=data['coherence_changed'];state=after
    return dict(geometric_sic_verified=True,geometric_sic_actions=count,
                geometric_sic_changed_states=changed,geometric_sic_maximum_inverse_residual=maximum_inverse)
