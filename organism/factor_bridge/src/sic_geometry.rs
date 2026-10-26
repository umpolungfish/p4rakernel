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
impl SicGeometry {
    pub fn prepare(width:usize,braid:&vox::gfe_circuit_braid::GfeCircuitBraidState)->Result<Self,String>{
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
        initial["rays"]=json!(frame.rays().iter().map(|ray|amplitudes(ray)).collect::<Vec<_>>());
        let dual=frame.prepare_exact_dual()?;
        Ok(Self{state:QuquartCarrier::from_control_amplitudes(format.clone(),z),
            frame,dual,width,format,initial,ticks:0})
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
        fields
    }
    pub fn observe(&mut self,context:&Value)->Result<(BelnapWord,bool,Value),String>{
        let before=values(&self.state);
        let p=field(context,"p")?;let q=field(context,"q")?;
        let signed_turns=field(context,"positive_turns")?-field(context,"negative_turns")?;
        let digits=self.width.div_ceil(2);
        let denominator=BigInt::one()<<(2*digits);
        let raw=&p-&q+&signed_turns;
        let numerator=((&raw%&denominator)+&denominator)%&denominator;
        let numerator=numerator.to_biguint().ok_or("negative normalized winding")?;
        let inverse=(&field(context,"clock")?%2u8)==BigInt::one();
        let phases=self.state.feedback_target_recorded(&numerator,digits)?;
        self.state.fourier_target(inverse);
        let after=values(&self.state);
        let mut returned=self.state.clone();
        returned.fourier_target(!inverse);
        let negative=if numerator.is_zero(){BigUint::zero()}else{
            denominator.to_biguint().unwrap()-&numerator};
        returned.feedback_target(&negative,digits)?;
        let inverse_state=values(&returned);
        let inverse_residual=before.iter().zip(&inverse_state).flat_map(|(a,b)|
            [(&a.re-&b.re).abs(),(&a.im-&b.im).abs()]).max().unwrap();
        let inverse_tolerance=BigInt::from(16u8);
        if inverse_residual>inverse_tolerance{return Err("SIC winding/Fourier inverse exceeds retained tolerance".into());}
        let observed=gram(&after);
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
        self.ticks+=1;
        Ok((BelnapWord::from_parity(&tape),reverse,json!({
            "schema":"retained-sic-coherence-rotation-v1","tick":self.ticks,
            "arm":context["arm"],"before":amplitudes(&before),"after":amplitudes(&after),
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
            "coherence_changed":gram(&before)!=observed,"leakage_retained":true})))
    }
}
