//! Exact paired source payload carried through the internal horn operation.
//! The two signed lifts share one source, operator, modular address and ancestry.
use super::{amplitudes,coordinates,field,gram,FixedComplex,FixedQuquartSic,PreparedSicDual};
use num_bigint::BigInt;
use num_traits::{One,Zero,Signed};
use serde_json::{json,Value};

pub struct Branch {
    pub inner:[FixedComplex;4],
    pub record:Value,
}
fn real(re:BigInt)->FixedComplex{FixedComplex{re,im:BigInt::zero()}}

/// Half-sum/difference is exact on the two odd factor lanes. Full integer
/// representatives are retained before taking any modular image.
pub fn prepare(context:&Value,width:usize)->Result<Vec<Branch>,String>{
    let n=field(context,"source")?;let p=field(context,"p")?;let q=field(context,"q")?;
    let period=BigInt::one()<<width;
    let h=field(context,"height")?;
    let h=if field(context,"negative")?.is_zero(){h}else{-h};
    if &p*&q!=&n+&h*&period{return Err("source metric lost signed carry relation".into());}
    if q<=BigInt::zero()||q>=period{return Err("source metric requires retained positive residue".into());}
    let mut branches=Vec::new();
    for (name,lift,height) in [("positive",q.clone(),h.clone()),
            ("complementary",&q-&period,&h-&p)]{
        let sum=&p+&lift;let difference=&p-&lift;
        if &sum%2u8!=BigInt::zero()||&difference%2u8!=BigInt::zero(){
            return Err("inner source split has nonintegral half coordinates".into());
        }
        let u=sum/2u8;let v=difference/2u8;
        let major_squared=&u*&u;let minor_squared=&v*&v+&n;
        let defect=&p*&lift-&n;
        if &major_squared-&minor_squared!=defect||defect!=&height*&period{
            return Err("source metric radius difference lost exact product defect".into());
        }
        let source=[real(p.clone()),real(BigInt::one()),real(lift.clone()),real(-BigInt::one())];
        let inner=[real(u.clone()),real(BigInt::zero()),real(v.clone()),real(BigInt::one())];
        let returned=fuse(&inner);
        if amplitudes(&returned)!=amplitudes(&source){return Err("inner source split/fuse lost its payload".into());}
        let source_gram=gram(&source);
        if &source_gram[2].0+&n*&source_gram[7].0!=defect{
            return Err("source Gram lost its product relation".into());
        }
        let record=json!({"lift":name,"source":n.to_string(),"p":p.to_string(),"q":lift.to_string(),
            "height":height.to_string(),"period":period.to_string(),
            "u":u.to_string(),"v":v.to_string(),"major_squared":major_squared.to_string(),
            "minor_squared":minor_squared.to_string(),"product_defect":defect.to_string(),
            "source_amplitudes":amplitudes(&source),"inner_amplitudes":amplitudes(&inner),
            "source_gram":coordinates(&source_gram),"split_fuse_verified":true,
            "source_context_retained":true});
        branches.push(Branch{inner,record});
    }
    Ok(branches)
}

/// Fuse the transformed internal coordinates; this is H A H/2 on the source
/// payload when A is the actual banked operator, with its denominator retained.
pub fn fuse(inner:&[FixedComplex;4])->[FixedComplex;4]{
    core::array::from_fn(|i|{
        let (a,b,subtract)=match i{0=>(0,2,false),1=>(1,3,false),2=>(0,2,true),_=>(1,3,true)};
        if subtract{FixedComplex{re:&inner[a].re-&inner[b].re,im:&inner[a].im-&inner[b].im}}
        else{FixedComplex{re:&inner[a].re+&inner[b].re,im:&inner[a].im+&inner[b].im}}
    })
}

fn gcd(mut a:BigInt,mut b:BigInt)->BigInt{
    a=a.abs();b=b.abs();while !b.is_zero(){let r=&a%&b;a=b;b=r;}a
}

/// Full complex SIC masses and dual act on the transformed source payload.
/// Candidate divisors come from its actual coordinates and weighted Gram.
pub fn observe(frame:&FixedQuquartSic,dual:&PreparedSicDual,n:&BigInt,
    inner:&[FixedComplex;4],denominator:&BigInt)->Result<(Option<BigInt>,Value),String>{
    let returned=fuse(inner);let observed=gram(&returned);
    let masses=frame.gram_mass_numerators(&observed)?;
    let recovered=dual.apply(frame,&masses)?;
    if observed.iter().zip(&recovered.numerators).any(|((a,b),(c,d))|
            &(a*&recovered.denominator)!=c||&(b*&recovered.denominator)!=d){
        return Err("source metric SIC dual lost transformed Gram".into());
    }
    let defect=(&observed[2].0+n*&observed[7].0,&observed[2].1+n*&observed[7].1);
    let mut divisors=Vec::new();let mut candidate=None;
    for value in returned.iter().flat_map(|z|[&z.re,&z.im]).chain([&defect.0,&defect.1]){
        let d=gcd(value.clone(),n.clone());
        if d>BigInt::one()&&&d<n&&candidate.is_none(){candidate=Some(d.clone());}
        divisors.push(d.to_string());
    }
    Ok((candidate,json!({"inner_after":amplitudes(inner),"fused_after":amplitudes(&returned),
        "amplitude_denominator":denominator.to_string(),"gram":coordinates(&observed),
        "weighted_product_gram":[defect.0.to_string(),defect.1.to_string()],
        "gram_denominator":(denominator*denominator).to_string(),
        "mass_numerators":masses.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "dual_numerators":coordinates(&recovered.numerators),
        "dual_denominator":recovered.denominator.to_string(),"coordinate_gcds":divisors,
        "exact_sic_return":true})))
}

/// Transport the real p coordinate of the fused source payload to Z/NZ.
/// The denominator is a power of two, hence a unit for the retained odd N.
/// The entire complex payload and the signed lift stay beside this projection.
pub fn rotation_readout(inner:&[FixedComplex;4],denominator:&BigInt,n:&BigInt)
    ->Result<BigInt,String>{
    if n%2u8!=BigInt::one(){return Err("source metric transport requires odd source".into());}
    let mut remaining=denominator.clone();let inverse_two=(n+1u8)/2u8;
    let mut inverse=BigInt::one();
    while remaining>BigInt::one(){
        if &remaining%2u8!=BigInt::zero(){return Err("source metric has a non-dyadic denominator".into());}
        remaining/=2u8;inverse=inverse*&inverse_two%n;
    }
    if remaining!=BigInt::one(){return Err("source metric denominator is not positive".into());}
    let value=&fuse(inner)[0].re*inverse;
    Ok((value%n+n)%n)
}
