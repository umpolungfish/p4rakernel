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
    count=changed=banked_actions=metric_actions=anchored_actions=0;maximum_inverse=0
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
        phase_p,phase_q=numeral('p'),numeral('q')
        if 'carried_torus_frame' in data:
            from torus_frames_replay import verify as verify_carried_frame
            phase_p,phase_q,frame_divisor=verify_carried_frame(data,context,n)
            frame=data['carried_torus_frame']
            assert frame['tick']==data['tick']
            if frame['schema'] in ('carried-source-height-torus-frame-v2','carried-source-height-torus-frame-v3') and frame['stage']=='frame-return':
                learned={f['name']:f['word'] for f in operation['learning_context']['fields']}
                spindle=frame['frames'][1]
                for channel in ['normal','outer','miniature','centreline']:
                    for i,value in enumerate(spindle[channel]):
                        assert int(learned[f'frame_{channel}_{i}']['numeral'])==int(value)
                assert int(learned['frame_exact_height_zero']['numeral'])==int(frame['exact_height_zero'])
            if frame_divisor is not None:
                assert int(data['source_divisor']['numeral'])==frame_divisor and n%frame_divisor==0
        numerator=(phase_p-phase_q+turns)%denominator
        assert int(data['winding_numerator'])==numerator
        assert int(data['winding_denominator'])==denominator
        assert int(data['signed_turns'])==turns
        assert data['fourier_inverse']==bool(numeral('clock')%2)
        coefficients=vector(data['winding_coefficients'])
        braid_roots=None
        if 'prime_braid' in data:
            from prime_braid_replay import verify as verify_prime_braid
            braid_roots=verify_prime_braid(data,context,n,bits)
        with mp.workprec(bits+80):
            for k,(re,im) in enumerate(coefficients):
                if data.get('cyclic_source_phase',{}).get('marked_channels',[False]*4)[k]:re,im=im,-re
                angle=-2*mp.pi*((numerator*k)%denominator)/denominator
                expected=mp.mpc(mp.cos(angle),mp.sin(angle))*scale
                if braid_roots is not None:
                    expected*=mp.mpc(*braid_roots[k])/scale
                tolerance=4 if braid_roots is not None else 2
                assert abs(re-int(mp.nint(expected.real)))<=tolerance
                assert abs(im-int(mp.nint(expected.imag)))<=tolerance
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
        exact_output=None
        if 'banked_frame' in data:
            banked_actions+=1
            bank=data['banked_frame'];w=bank['frame']
            assert bank['register_cells']==3*width
            assert bank['wires']==[level,width+level]
            address_base=numeral('q')|(numeral('p')<<width)|(n<<(2*width))
            address_base &= ~(1<<level);address_base &= ~(1<<(width+level))
            addresses=[address_base|((label&1)<<level)|((label//2)<<(width+level)) for label in range(4)]
            assert list(map(int,bank['addresses']))==addresses
            matrix=vector(bank['matrix']);dual=vector(bank['dual'])
            diagonal=[(-b,a) if sign else(a,b) for (a,b),sign in zip(coefficients,signs)]
            def rotate(z,k):
                a,b=z;return [(a,b),(-b,a),(-a,-b),(b,-a)][k%4]
            def product(z,v):
                a,b=z;c,d=v;return a*c-b*d,a*d+b*c
            def action(matrix,state):
                return [tuple(sum(product(matrix[4*row+col],state[col])[k] for col in range(4)) for k in range(2)) for row in range(4)]
            expected_matrix=[rotate(diagonal[col],(-row*col if data['fourier_inverse'] else row*col)) for row in range(4) for col in range(4)]
            assert matrix==expected_matrix
            norms=[a*a+b*b for a,b in diagonal];total=1
            for norm in norms:total*=norm
            normalization=(4*total,0)
            assert tuple(map(int,bank['dual_normalization']))==normalization
            for row in range(4):
                for col in range(4):
                    value=tuple(sum(product(dual[4*row+i],matrix[4*i+col])[k] for i in range(4)) for k in range(2))
                    assert value==(normalization if row==col else (0,0))
            exact_output=action(matrix,state)
            assert vector(bank['exact_output'])==exact_output
            assert action(dual,exact_output)==[(a*normalization[0],b*normalization[0]) for a,b in state]
            assert w['partition_masks']==[1,2,12]
            if anchor:=w.get('anchored_return'):
                anchored_actions+=1
                if anchor.get('exposed_final_morphism'):
                    if anchor['word']=='≺∋⊣⊣∈⊤≺≻≻≻':
                        assert anchor['exposed_final_morphism']=='AFWD' and anchor['live_register']=='T'
                        assert anchor['anchor_nodes']==[2,3] and anchor['output_node']==9
                        assert anchor['live_clear_positions']==[0,6] and anchor['live_payload_empty']
                        assert anchor['seeded_live_support'] and w['live_clear_position']==6
                        assert w['ancestry_pair']==[4,1]
                        assert w['nodes']==['AREV','FFUSE3','TANCH','TANCH','FSPLIT3','EVALT','AREV','AFWD','AFWD','AFWD']
                        assert w['edges']==[[0,1],[1,2],[2,3],[3,4],[4,5],[5,6],[6,7],[4,8],[4,9]]
                        assert bank['cut_execution']==dict(word='≺∋⊣⊣∈⊤≺≻≻≻',register=1,deposits=1,cleared=1,restored=0,seeded=1)
                    else:
                        assert anchor['word']=='∋⊣⊣∈⊤≻≻≻≺'
                        assert anchor['exposed_final_morphism']=='AREV' and anchor['live_register']=='N'
                        assert anchor['anchor_nodes']==[1,2] and anchor['output_node']==8
                        assert w['live_clear_position']==8 and w['ancestry_pair']==[3,0]
                        assert w['nodes']==['FFUSE3','TANCH','TANCH','FSPLIT3','EVALT','AFWD','AFWD','AFWD','AREV']
                        assert w['edges']==[[0,1],[1,2],[2,3],[3,4],[4,5],[3,6],[3,7],[5,8]]
                        assert bank['cut_execution']==dict(word='∋⊣⊣∈⊤≻≻≻≺',register=0,deposits=1,cleared=1,restored=0)
                    assert anchor['deposited_support']=='T' and anchor['pending_leading_fuse']
                    assert anchor['pair_crosses_cut']
                    assert data['pending_leading_fuses']==3
                    resumed=data['resumed_leading_fuses']
                    assert len(resumed)==(0 if data['tick']==1 else 3)
                    assert all(r['operation']=='leading FFUSE' and r['same_arena'] and r['exact_amplitude_return'] for r in resumed)
                else:
                    assert w['ancestry_pair']==[2,7] and w['live_clear_position']==6
                    assert w['nodes'][:2]==['TANCH','TANCH']
                    expected_edges=[[0,1],[1,2],[2,3],[2,4],[2,5],[3,6],[6,7],[4,7],[5,7]]
                    if anchor.get('open_output'):
                        assert anchor['open_input_node']==0 and not anchor['feedback_edge']
                    else:expected_edges.append([7,0])
                    assert w['edges']==expected_edges
                    assert anchor['word']=='⊣⊣∈≻≻≻≺∋' and anchor['anchor_nodes']==[0,1]
                    assert anchor['output_node']==7
                assert anchor['source_start']==2*width
                assert anchor['source_width']==width and int(anchor['source'])==n
                assert anchor['source_preserved'] and anchor['same_arena'] and anchor['output_before_fixation']
                assert bank['output_port_consumed']
            else:assert w['ancestry_pair']==[1,6]
            assert w['exact_split_return'] and w['live_register_cleared'] and w['exact_banked_return']
            assert w['exact_transformed_return'] and w['exact_dual_return_after_determinant_normalization']
            split=[[(a,b) if mask&(1<<i) else (0,0) for i,(a,b) in enumerate(state)] for mask in w['partition_masks']]
            assert list(map(int,w['split_mass']))==[sum(a*a+b*b for a,b in z) for z in split]
            banks=[action(matrix,z) for z in split];banks.append([(0,0)]*4)
            fused=[tuple(sum(z[i][k] for z in banks) for k in range(2)) for i in range(4)]
            assert fused==exact_output
            cross=[(sum(a*c+b*d for (a,b),(c,d) in zip(left,right)),sum(a*d-b*c for (a,b),(c,d) in zip(left,right))) for left in banks for right in banks]
            assert cross==[(int(v['re']),int(v['im'])) for v in w['cross_arm_gram']]
            if any(a or b for a,b in split[2]):assert w['information_arm_loss_detected']
            action_den=2*scale;assert int(data['action_denominator'])==action_den
            def terminal(v):return (-1 if v<0 else 1)*((abs(v)+action_den//2)//action_den)
            after=[(terminal(a),terminal(b)) for a,b in exact_output]
        else:
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
        if exact_output is not None:
            for i,(re,im) in enumerate(exact_output):
                for name,value in [(f'sic_banked_re_{i}',abs(re)),(f'sic_banked_im_{i}',abs(im)),
                                   (f'sic_banked_re_negative_{i}',int(re<0)),(f'sic_banked_im_negative_{i}',int(im<0))]:
                    assert int(learned[name]['numeral'])==value
            assert int(learned['sic_banked_denominator']['numeral'])==2*scale
        observed=gram(exact_output if exact_output is not None else after);assert vector(data['gram'])==observed
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
        if 'source_metric' in data:
            from source_metric_replay import verify as verify_source_metric
            verify_source_metric(data,context,n,projectors)
            metric_actions+=1
        selected=lift;selected_reverse=data['reverse']
        if 'frame_rotation' in data:
            from math import gcd
            f=data['frame_rotation'];modulus=1<<width
            value=lambda name:int(f[name]['numeral'])
            raw=int(data.get('source_metric_rotation_readout',data['carried_torus_frame']['readout_parameters'][0]))
            target=((raw%(1<<width))&~7)|(numeral('p')&7)
            step_forward=int(context['rotation_step']['numeral'])
            assert value('raw_readout')==raw and value('input_p')==numeral('p')
            assert value('target')==target==value('recovered_target')
            relative=target*pow(numeral('p'),-1,modulus)%modulus
            assert value('relative')==relative and value('step')==step_forward
            frame_lift=value('lift');assert 0<=frame_lift<period
            assert pow(step_forward,frame_lift,modulus)==relative
            assert value('target_gcd')==gcd(target,n)
            assert f['coset_preserved'] and f['source_bank_retained'] and f['inverse_verified']
            net=frame_lift+(-lift if data['reverse'] else lift)
            if data.get('full_signed_rotation_word_retained'):
                selected=abs(net);selected_reverse=net<0
            else:
                selected=net%period;selected_reverse=False
            if data.get('source_divisor_origin')=='normal-frame-rotation-target':
                assert int(data['source_divisor']['numeral'])==gcd(target,n) and 1<gcd(target,n)<n
        if 'selected_rotation_lift' in data:
            assert int(data['selected_rotation_lift']['numeral'])==selected
            assert data['selected_rotation_reverse']==selected_reverse
        rotation=data['rotation'];transition=rotation['transition']
        assert rotation['arm']==context['arm']==event['arm']
        assert int(transition['lift']['numeral'])==selected and transition['reverse']==selected_reverse
        previous=transition['before'];assert int(previous['p']['numeral'])==numeral('p')
        assert int(previous['q']['numeral'])==numeral('q')
        modulus=1<<width;torus=task['toroidal_division']
        step=int(torus['inverse_step' if selected_reverse else 'step']['numeral'])
        back=int(torus['step' if selected_reverse else 'inverse_step']['numeral'])
        assert int(transition['after_p']['numeral'])==numeral('p')*pow(step,selected,modulus)%modulus
        assert int(transition['after_q']['numeral'])==numeral('q')*pow(back,selected,modulus)%modulus
        assert data['coherence_changed']==(gram(state)!=gram(after))
        changed+=data['coherence_changed'];state=after
    from source_return_replay import verify as verify_source_return
    result=dict(**verify_source_return(task,n),geometric_sic_verified=True,geometric_sic_actions=count,
                geometric_sic_changed_states=changed,geometric_sic_maximum_inverse_residual=maximum_inverse,
                carried_torus_frame_actions=sum('carried_torus_frame' in o['toroidal_operation'].get('geometric_sic',{}) for o in task['operations']),
                banked_sic_frame_actions=banked_actions,banked_sic_frame_exact_returns=banked_actions)
    result['prime_braid_actions']=sum('prime_braid' in o['toroidal_operation'].get('geometric_sic',{}) for o in task['operations'])
    if metric_actions:result.update(source_metric_return_verified=True,source_metric_actions=metric_actions,
        signed_source_copy_returns=2*metric_actions,anchored_output_port_actions=anchored_actions)
    return result
