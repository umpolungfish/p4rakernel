//! Compact source square-wave paths on the current two factor alternatives.
//! A label is an unverified well until exact factor closure. No prime table,
//! reference factors, expanded path array or bit permutation supplies it.
use super::{amplitudes,field,FixedComplex,FixedPointFormat};
use num_bigint::{BigInt,BigUint};
use num_traits::{Zero,ToPrimitive};
use serde_json::{json,Value};

fn path(label:&BigInt,ordinal:&BigInt,format:&FixedPointFormat)
    ->Result<([FixedComplex;2],Value),String>{
    if label<=&BigInt::zero()||ordinal<&BigInt::zero(){return Err("invalid source well address".into());}
    // The native source has 20 horizontal samples and 10 connector samples
    // in each of 4*m segments, at velocity ratio one (m=label).
    let segment=ordinal/30u8;let sample=(ordinal%30u8).to_usize().unwrap();
    let quadrant=(&segment%4u8).to_usize().unwrap();
    let levels=[11i32,0,-11,0];
    let (azimuth_num,azimuth_den,tube_num,tube_den,drift_num)=if sample<20 {
        (&segment*19u8+sample,label*76u8,BigInt::from(levels[quadrant]),BigInt::from(40u8),0usize)
    }else{
        let j=sample-20;
        ((&segment+1u8),label*4u8,
         BigInt::from(levels[quadrant])*(9-j)+BigInt::from(levels[(quadrant+1)%4])*j,
         BigInt::from(360u16),j)
    };
    let alpha=FixedComplex::winding_twiddle(&azimuth_num,&azimuth_den.to_biguint().unwrap(),format)?;
    let drift=FixedComplex::connector_twiddle(&BigInt::from(drift_num),&BigUint::from(450u16),format)?;
    let alpha=alpha.mul(&drift,format);
    let theta=FixedComplex::winding_twiddle(&tube_num,&tube_den.to_biguint().unwrap(),format)?;
    let scale=format.scale();
    // One common denominator scale^2 for all spatial coordinates. Keep
    // source directions at the poles and both complementary inner points.
    let direction=[&alpha.re*&scale,&alpha.im*&scale,BigInt::zero()];
    let normal=[&alpha.re*&theta.re,&alpha.im*&theta.re,&theta.im*&scale];
    let plus:[BigInt;3]=core::array::from_fn(|i|&normal[i]+&direction[i]);
    let minus:[BigInt;3]=core::array::from_fn(|i|&normal[i]-&direction[i]);
    let recovered_direction:[BigInt;3]=core::array::from_fn(|i|(&plus[i]-&minus[i])/2u8);
    let recovered_normal:[BigInt;3]=core::array::from_fn(|i|(&plus[i]+&minus[i])/2u8);
    if recovered_direction!=direction||recovered_normal!=normal{return Err("source braid lost its inner-horn return".into());}
    let recovered_alpha=FixedComplex{re:&recovered_direction[0]/&scale,im:&recovered_direction[1]/&scale};
    let negative_theta=FixedComplex{re:theta.re.clone(),im:-&theta.im};
    let roots=[recovered_alpha.mul(&theta,format),recovered_alpha.mul(&negative_theta,format)];
    let strings=|v:&[BigInt;3]|v.iter().map(ToString::to_string).collect::<Vec<_>>();
    let frames=[("horn",2u8),("spindle",1u8),("sphere",0u8)].into_iter().map(|(name,r)|{
        let outer: [BigInt;3]=core::array::from_fn(|i|&direction[i]*r+&normal[i]*2u8);
        let original_inner:[BigInt;3]=core::array::from_fn(|i|(&direction[i]+&normal[i])*r);
        json!({"name":name,"R":r,"r":2,"outer":strings(&outer),"original_inner":strings(&original_inner)})
    }).collect::<Vec<_>>();
    let period=label*120u8;
    Ok((roots.clone(),json!({"label":label.to_string(),"label_status":"unverified-factor-alternative",
        "velocity_ratio":[1,1],"segments":(label*4u8).to_string(),"samples":period.to_string(),
        "ordinal":ordinal.to_string(),"segment":segment.to_string(),"sample":sample,
        "completed_paths":(ordinal/&period).to_string(),"quadrant":quadrant,
        "azimuth_turns":[azimuth_num.to_string(),azimuth_den.to_string()],
        "connector_radians":[drift_num.to_string(),"450"],
        "tube_turns":[tube_num.to_string(),tube_den.to_string()],
        "negative_sheet_map":"(azimuth+1/2,1/2-tube)",
        "azimuth_root":[alpha.re.to_string(),alpha.im.to_string()],
        "tube_root":[theta.re.to_string(),theta.im.to_string()],
        "spatial_denominator":(&scale*&scale).to_string(),"frames":frames,
        "sphere_inner_plus":strings(&plus),"sphere_inner_minus":strings(&minus),
        "returned_direction":strings(&recovered_direction),"returned_normal":strings(&recovered_normal),
        "inner_return_verified":true,"phase_input_from_inner_return":true,
        "roots":roots.iter().map(|z|[z.re.to_string(),z.im.to_string()]).collect::<Vec<_>>()})))
}

pub fn observe(context:&Value,format:&FixedPointFormat)->Result<([FixedComplex;4],Value),String>{
    let p=field(context,"p")?;let q=field(context,"q")?;let clock=field(context,"clock")?;
    // Address each well by its carried partner and the resident clock. The
    // original ordered path remains implicit and arbitrary addresses work.
    let(a,left)=path(&p,&(&q+&clock),format)?;
    let(b,right)=path(&q,&(&p+&clock),format)?;
    let roots=[a[0].clone(),a[1].clone(),b[0].clone(),b[1].clone()];
    Ok((roots.clone(),json!({"schema":"source-square-wave-joint-braid-v1",
        "source":field(context,"source")?.to_string(),"clock":clock.to_string(),
        "source_generator":"ig-docs/torus_process.py:square_wave_angles",
        "well_order":["p","q"],"channel_order":["p-positive","p-negative","q-positive","q-negative"],
        "paths":[left,right],"roots":amplitudes(&roots),
        "operator":"joint angular diagonal before retained Fourier/split-fuse",
        "input_boundary":"resident p/q alternatives derived from N"})))
}
