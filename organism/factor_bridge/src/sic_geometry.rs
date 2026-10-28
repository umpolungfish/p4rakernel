//! Retained complex evaluator state coupled to the same paired source orbit.
//! The normalized imaginary coherence is an experimental rotation coordinate;
//! exact source division, not this projection, decides factor closure.
use g_momonados::{anyon_ququart::{FixedQuquartSic,PreparedSicDual,QuquartCarrier},
    anyon_pair::COMPUTATIONAL_CHANNELS,phase_unbraid::{FixedComplex,FixedPointFormat}};
use num_bigint::{BigInt,BigUint};
use num_traits::{One,Zero,Signed};
use serde_json::{json,Value};
use vox::{belnap_word::BelnapWord,morphism_factor as mf};

pub struct SicGeometry {
    state:QuquartCarrier,frame:FixedQuquartSic,dual:PreparedSicDual,
    width:usize,format:FixedPointFormat,initial:Value,ticks:usize,
    last_exact_output:Option<([FixedComplex;4],BigInt)>,
    source_return:vox::geometric_return::SourceRingReturn,
    cyclic_word:Vec<char>,cyclic_landings:Vec<u8>,
    last_carried_frame:Option<Value>,
}
fn values(state:&QuquartCarrier)->[FixedComplex;4]{
    core::array::from_fn(|i|state.amplitudes()[COMPUTATIONAL_CHANNELS[i]].clone())
}
fn amplitudes(z:&[FixedComplex;4])->Value{
    json!(z.iter().map(|v|[v.re.to_string(),v.im.to_string()]).collect::<Vec<_>>())
}
fn gram(z:&[FixedComplex;4])->[(BigInt,BigInt);16]{
    core::array::from_fn(|i|{
        let(a,b)=(&z[i/4],&z[i%4]);
        (&a.re*&b.re+&a.im*&b.im,&a.re*&b.im-&a.im*&b.re)
    })
}
fn coordinates(z:&[(BigInt,BigInt);16])->Value{
    json!(z.iter().map(|(re,im)|[re.to_string(),im.to_string()]).collect::<Vec<_>>())
}
fn field(context:&Value,name:&str)->Result<BigInt,String>{
    let value=context["fields"].as_array().ok_or("SIC input lost context fields")?.iter()
        .find(|f|f["name"]==name).ok_or("SIC input lost a numerical field")?;
    let numeral=value["word"]["numeral"].as_str().ok_or("SIC numerical boundary remains unresolved")?;
    numeral.parse().map_err(|_|"SIC numerical context is malformed".into())
}
fn quarter(z:&FixedComplex,k:usize)->FixedComplex{
    match k%4 {0=>z.clone(),1=>FixedComplex{re:-&z.im,im:z.re.clone()},
        2=>FixedComplex{re:-&z.re,im:-&z.im},_=>FixedComplex{re:z.im.clone(),im:-&z.re}}
}
/// Lift the current factor-cell alternatives into the existing exact banked
/// frame. Only four source-bound basis branches are present, never the full
/// product relation. Their control cells are the selected p/q cells themselves.
fn banked_transform(context:&Value,width:usize,before:&[FixedComplex;4],
    phases:&[FixedComplex;4],marked:[bool;4],inverse:bool)
    ->Result<([FixedComplex;4],Value),String>{
    use g_momonados::{ququart_decision::DecisionArena,resident_frame};
    let level=context["source_fibre"]["level"].as_u64().ok_or("missing source fibre level")? as usize;
    let p=field(context,"p")?.to_biguint().ok_or("negative p")?;
    let q=field(context,"q")?.to_biguint().ok_or("negative q")?;
    let source=field(context,"source")?.to_biguint().ok_or("negative source")?;
    let wires=[level,width+level];
    let mut base=&q+(&p<<width)+(&source<<(2*width));
    base.set_bit(wires[0] as u64,false);base.set_bit(wires[1] as u64,false);
    let addresses:[BigUint;4]=core::array::from_fn(|label|{
        let mut address=base.clone();address.set_bit(wires[0] as u64,label&1!=0);
        address.set_bit(wires[1] as u64,label&2!=0);address});
    let diagonal:[FixedComplex;4]=core::array::from_fn(|i|quarter(&phases[i],usize::from(marked[i])));
    let norms:[BigInt;4]=core::array::from_fn(|i|&diagonal[i].re*&diagonal[i].re+&diagonal[i].im*&diagonal[i].im);
    if norms.iter().any(Zero::is_zero){return Err("banked winding operator has a zero phase norm".into());}
    let product=norms.iter().fold(BigInt::one(),|v,n|v*n);
    let exponent=|row:usize,col:usize|if inverse{(4-(row*col)%4)%4}else{row*col%4};
    let matrix:[(BigInt,BigInt);16]=core::array::from_fn(|i|{
        let z=quarter(&diagonal[i%4],exponent(i/4,i%4));(z.re,z.im)});
    let dual:[(BigInt,BigInt);16]=core::array::from_fn(|i|{
        let row=i/4;let col=i%4;
        let z=quarter(&FixedComplex{re:diagonal[row].re.clone(),im:-&diagonal[row].im},
            (4-exponent(col,row))%4);
        let factor=&product/&norms[row];(z.re*&factor,z.im*&factor)});
    let normalization=(&product*4u8,BigInt::zero());
    let mut arena=DecisionArena::new(3*width);
    let mut root=arena.zero();
    for (address,z) in addresses.iter().zip(before){
        let basis=arena.basis(address,BigInt::one());
        let branch=arena.scale_complex_numerator(basis,&(z.re.clone(),z.im.clone()));
        root=arena.sum(root,branch);
    }
    let (returned,witness)=resident_frame::apply_full(&mut arena,root,wires,&matrix,&dual,&normalization)?;
    let output=core::array::from_fn(|i|{
        let(re,im)=arena.amplitude(returned,&addresses[i]);FixedComplex{re,im}});
    let observed=arena.belnap_gram(returned,arena.belnap_coordinate(wires)?);
    if observed!=gram(&output){return Err("banked SIC output lost factor-cell coherence".into());}
    let output_record=amplitudes(&output);
    Ok((output,json!({"frame":witness.record(),"register_cells":3*width,
        "payload_layout":"q[0:w],p[w:2w],source[2w:3w]","wires":wires,
        "addresses":addresses.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "matrix":coordinates(&matrix),"dual":coordinates(&dual),
        "dual_normalization":[normalization.0.to_string(),"0"],
        "operator_denominator":"2*fixed_point_scale","exact_output":output_record,
        "input_context_retained":true})))
}
impl SicGeometry {
    pub fn prepare(width:usize,braid:&vox::gfe_circuit_braid::GfeCircuitBraidState,source:&[char])->Result<Self,String>{
        let source_n:BigUint=mf::dec_of(source).parse().map_err(|_|"invalid cyclic source")?;
        let packets=vox::combined_factor::hex_word(&source_n);
        let mut cyclic_word=vec!['⊢'];
        cyclic_word.extend(packets.chars().filter(|c| !matches!(c,'⊢'|'⊣')));
        cyclic_word.push('⊣');
        let mut cyclic_landings=Vec::with_capacity(cyclic_word.len());
        for cut in 0..cyclic_word.len(){
            let rotated:String=cyclic_word.iter().cycle().skip(cut).take(cyclic_word.len()).collect();
            cyclic_landings.push(vox::phase_word::execute(&rotated,&())?.register);
        }
        let format=FixedPointFormat::for_modulus_bits(width.saturating_sub(1) as u64)?;
        let mut z=core::array::from_fn(|_|FixedComplex{re:BigInt::zero(),im:BigInt::zero()});
        for(i,value)in braid.output.iter().enumerate(){
            z[i]=FixedComplex::from_f64(value.re,value.im,&format)?;
        }
        let mut initial=json!({"basis":"prepared GFE coordinate order 2*p+q",
            "input_boundary":"source-prepared QFT1+HTSX state",
            "amplitudes":amplitudes(&z),"fractional_bits":format.w_bits,
            "braid_word":braid.braid_word});
        let frame=FixedQuquartSic::new(&format)?;
        initial["cyclic_source_word"]=json!(cyclic_word.iter().collect::<String>());
        initial["cyclic_source_landings"]=json!(cyclic_landings);
        initial["rays"]=json!(frame.rays().iter().map(|ray|amplitudes(ray)).collect::<Vec<_>>());
        let dual=frame.prepare_exact_dual()?;
        Ok(Self{state:QuquartCarrier::from_control_amplitudes(format.clone(),z),
            frame,dual,width,format,initial,ticks:0,last_exact_output:None,source_return:vox::geometric_return::SourceRingReturn::prepare(source),cyclic_word,cyclic_landings,last_carried_frame:None})
    }
    pub fn preparation(&self)->Value{self.initial.clone()}
    pub fn learning_fields(&self)->Vec<Value>{
        let mut fields=Vec::new();
        let mut push=|name:String,value:BigInt| {
            let tape=mf::decimal_to_tape(&value.to_string()).expect("definite SIC context numeral");
            fields.push(json!({"name":name,"word":vox::toroidal_division::word(&BelnapWord::from_parity(&tape))}));
        };
        for(i,z)in values(&self.state).iter().enumerate(){
            push(format!("sic_re_{i}"),z.re.abs());push(format!("sic_im_{i}"),z.im.abs());
            push(format!("sic_re_negative_{i}"),BigInt::from(u8::from(z.re.is_negative())));
            push(format!("sic_im_negative_{i}"),BigInt::from(u8::from(z.im.is_negative())));
        }
        push("sic_tick".into(),BigInt::from(self.ticks));
        push("sic_fractional_bits".into(),BigInt::from(self.format.w_bits));
        let (exact,denominator)=self.last_exact_output.clone().unwrap_or((values(&self.state),BigInt::one()));
        for(i,z)in exact.iter().enumerate(){
            push(format!("sic_banked_re_{i}"),z.re.abs());push(format!("sic_banked_im_{i}"),z.im.abs());
            push(format!("sic_banked_re_negative_{i}"),BigInt::from(u8::from(z.re.is_negative())));
            push(format!("sic_banked_im_negative_{i}"),BigInt::from(u8::from(z.im.is_negative())));
        }
        push("sic_banked_denominator".into(),denominator);
        if let Some(record)=&self.last_carried_frame {
            if record["stage"]=="frame-return" {
                let spindle=&record["frames"][1];
                for channel in ["normal","outer","miniature","centreline"] {
                    for (i,value) in spindle[channel].as_array().unwrap().iter().enumerate() {
                        push(format!("frame_{channel}_{i}"),value.as_str().unwrap().parse().unwrap());
                    }
                }
                push("frame_exact_height_zero".into(),BigInt::from(u8::from(record["exact_height_zero"].as_bool().unwrap_or(false))));
            }
        }
        fields.extend(self.source_return.learning_fields());
        fields
    }
    pub fn observe(&mut self,context:&Value)->Result<(BelnapWord,bool,Value),String>{
        let before=values(&self.state);

        let signed_turns=field(context,"positive_turns")?-field(context,"negative_turns")?;
        let digits=self.width.div_ceil(2);
        let denominator=BigInt::one()<<(2*digits);
        let (frame_p,frame_height,frame_divisor,carried_frame)=vox::carried_torus_frame::observe(context,self.ticks+1)?;
        let frame_p:BigInt=mf::dec_of(&frame_p.to_parity().map_err(str::to_string)?).parse().map_err(|_|"frame p readout")?;
        let frame_height:BigInt=mf::dec_of(&frame_height.to_parity().map_err(str::to_string)?).parse().map_err(|_|"frame height readout")?;
        let raw=&frame_p-&frame_height+&signed_turns;
        let numerator=((&raw%&denominator)+&denominator)%&denominator;
        let numerator=numerator.to_biguint().ok_or("negative normalized winding")?;
        let inverse=(&field(context,"clock")?%2u8)==BigInt::one();
        let fibre=&context["source_fibre"];
        if fibre["enclosure"]!="B" {return Err("SIC source fibre lost its enclosing B".into());}
        let rows=fibre["rows"].as_array().ok_or("SIC source fibre lost alternatives")?;
        if rows.len()!=4{return Err("SIC source fibre requires all four alternatives".into());}
        let mut source_marked=[false;4];
        for (k,row) in rows.iter().enumerate(){
            source_marked[k]=match row["evidence"].as_str(){
                Some("T")=>true,Some("F")=>false,
                _=>return Err("source phase requires an explicit definite congruence boundary".into()),
            };
        }
        if source_marked.iter().filter(|v|**v).count()!=2{
            return Err("odd source fibre lost its two correlated lifts".into());
        }
        self.state.phase_quarter_target(source_marked,false);
        let marked=values(&self.state);
        let mut phases=self.state.feedback_target_recorded(&numerator,digits)?;
        let cut=(&field(context,"clock")?%BigInt::from(self.cyclic_word.len())).to_string().parse::<usize>().map_err(|_|"invalid cyclic clock cut")?;
        let landing=self.cyclic_landings[cut];
        let cyclic_marked=core::array::from_fn(|i|landing&(1<<i)!=0);
        self.state.phase_quarter_target(cyclic_marked,false);
        for i in 0..4{if cyclic_marked[i]{phases[i]=quarter(&phases[i],1);}}
        let (exact_output,banked_frame)=banked_transform(context,self.width,&before,&phases,source_marked,inverse)?;
        let action_denominator=(BigInt::one()<<self.format.w_bits as usize)*2u8;
        let read_pairs=|key:&str|->[(BigInt,BigInt);16]{core::array::from_fn(|i|(
            banked_frame[key][i][0].as_str().unwrap().parse().unwrap(),
            banked_frame[key][i][1].as_str().unwrap().parse().unwrap()))};
        let normalization=banked_frame["dual_normalization"][0].as_str().unwrap().parse().unwrap();
        let before_pairs=core::array::from_fn(|i|(before[i].re.clone(),before[i].im.clone()));
        let (ring_divisor,source_return)=self.source_return.advance(
            &read_pairs("matrix"),&read_pairs("dual"),&normalization,&action_denominator,&before_pairs)?;

        let source_divisor=frame_divisor.or(ring_divisor);

        let rounded=|v:&BigInt|{
            let magnitude=(v.abs()+(&action_denominator/2u8))/&action_denominator;
            if v.is_negative(){-magnitude}else{magnitude}
        };
        let after=core::array::from_fn(|i|FixedComplex{
            re:rounded(&exact_output[i].re),im:rounded(&exact_output[i].im)});
        self.state=QuquartCarrier::from_control_amplitudes(self.format.clone(),after.clone());
        let mut returned=self.state.clone();
        returned.fourier_target(!inverse);
        let negative=if numerator.is_zero(){BigUint::zero()}else{
            denominator.to_biguint().unwrap()-&numerator};
        returned.feedback_target(&negative,digits)?;
        returned.phase_quarter_target(cyclic_marked,true);
        returned.phase_quarter_target(source_marked,true);
        let inverse_state=values(&returned);
        let inverse_residual=before.iter().zip(&inverse_state).flat_map(|(a,b)|
            [(&a.re-&b.re).abs(),(&a.im-&b.im).abs()]).max().unwrap();
        let inverse_tolerance=BigInt::from(16u8);
        if inverse_residual>inverse_tolerance{return Err("SIC winding/Fourier inverse exceeds retained tolerance".into());}
        let observed=gram(&exact_output);
        let masses=self.frame.gram_mass_numerators(&observed)?;
        let analytic=self.frame.certify_gram_frame_unrounded_masses(&observed,&masses)?;
        let exact=self.dual.apply(&self.frame,&masses)?;
        if observed.iter().zip(&exact.numerators).any(|((re,im),(x,y))|
            x!=&(re*&exact.denominator)||y!=&(im*&exact.denominator)){
            return Err("SIC exact dual lost a carried complex coordinate".into());
        }
        let trace=(0..4).fold(BigInt::zero(),|sum,i|sum+&exact.numerators[5*i].0);
        if trace<=BigInt::zero(){return Err("SIC readout has no retained evaluator mass".into());}
        let coherence=&exact.numerators[1].1;
        let period=BigInt::one()<<(self.width-3);
        let projected=&period*coherence.abs();
        let lift=&projected/&trace;let remainder=&projected%&trace;
        let reverse=coherence.is_negative();
        let tape=mf::decimal_to_tape(&lift.to_string()).ok_or("SIC lift numeral conversion failed")?;
        self.last_exact_output=Some((exact_output.clone(),action_denominator.clone()));
        self.last_carried_frame=Some(carried_frame.clone());
        self.ticks+=1;
        Ok((BelnapWord::from_parity(&tape),reverse,json!({
            "schema":"retained-sic-banked-factor-cell-rotation-v4","tick":self.ticks,
            "arm":context["arm"],"before":amplitudes(&before),"after":amplitudes(&after),
            "source_fibre":fibre,"source_phase_marked":source_marked,"source_phase_quarter_turns":1,
            "source_phase_after":amplitudes(&marked),
            "cyclic_source_phase":{"cut_selector":"retained-clock","cut":cut,"modulus":self.cyclic_word.len(),
                "landing_runtime_mask":landing,"marked_channels":cyclic_marked,"quarter_turns":1},
            "banked_frame":banked_frame,"action_denominator":action_denominator.to_string(),
            "carried_torus_frame":carried_frame,
            "source_return":source_return,"source_divisor":source_divisor.as_ref().map(vox::toroidal_division::word),
            "inverse_return":amplitudes(&inverse_state),"inverse_residual":inverse_residual.to_string(),
            "inverse_tolerance":inverse_tolerance.to_string(),"fourier_inverse":inverse,
            "winding_numerator":numerator.to_string(),"winding_denominator":denominator.to_string(),
            "winding_coefficients":amplitudes(&phases),
            "signed_turns":signed_turns.to_string(),"gram":coordinates(&observed),
            "mass_numerators":masses.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "exact_dual_numerators":coordinates(&exact.numerators),"exact_dual_denominator":exact.denominator.to_string(),
            "analytic_residual":analytic.rounded.maximum_residual.to_string(),
            "analytic_tolerance":analytic.rounded.tolerance.to_string(),
            "analytic_signed_residuals":coordinates(&analytic.signed_residual_numerators),
            "analytic_denominator":analytic.denominator.to_string(),
            "readout":"floor(orbit_period*abs(Im Gram[0,1])/trace Gram)",
            "orbit_period":period.to_string(),"projection_remainder":remainder.to_string(),
            "lift":lift.to_string(),"reverse":reverse,
            "coherence_changed":gram(&before)!=gram(&after),"leakage_retained":true})))
    }
}
