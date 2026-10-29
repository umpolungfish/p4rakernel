//! N-only horn rotor, prime windings, inner return and full SIC readout.
//! The feature excludes the legacy factor task at compile time.
use std::ffi::{c_char,c_void,CStr,CString};
use std::time::{Instant,Duration};
use num_bigint::{BigInt,BigUint};
use num_traits::{One,Zero};
use serde_json::{Value,json};
use g_momonados::{phase_unbraid::{FixedPointFormat,FixedComplex},anyon_ququart::{FixedQuquartSic,PreparedSicDual}};
use vox::morphism_factor as mf;
type Point=[BigUint;3];
fn point(p:&Point)->Value{json!(p.iter().map(ToString::to_string).collect::<Vec<_>>())}
fn gcd(mut a:BigUint,mut b:BigUint)->BigUint{while !b.is_zero(){let r=&a%&b;a=b;b=r;}a}
fn subtract(a:&BigUint,b:&BigUint,n:&BigUint)->BigUint{(a+n-b)%n}
fn compose(a:&Point,b:&Point,n:&BigUint)->Point{
    [subtract(&(&a[0]*&b[0]%n),&(&a[1]*&b[1]%n),n),
     (&a[0]*&b[1]+&a[1]*&b[0])%n,&a[2]*&b[2]%n]
}
fn power(p:&Point,mut exponent:u64,n:&BigUint)->Point{
    let mut a=p.clone();let mut r=[BigUint::one(),BigUint::zero(),BigUint::one()];
    while exponent>0{if exponent&1==1{r=compose(&r,&a,n);}exponent>>=1;if exponent>0{a=compose(&a,&a,n);}}
    r
}
fn norm(p:&Point,n:&BigUint)->bool{(&p[0]*&p[0]+&p[1]*&p[1])%n==&p[2]*&p[2]%n}
fn gram(z:&[FixedComplex;4])->Vec<(BigInt,BigInt)>{
    (0..16).map(|i|{let(a,b)=(&z[i/4],&z[i%4]);
        (&a.re*&b.re+&a.im*&b.im,&a.re*&b.im-&a.im*&b.re)}).collect()
}
fn coords(v:&[(BigInt,BigInt)])->Value{json!(v.iter().map(|(a,b)|[a.to_string(),b.to_string()]).collect::<Vec<_>>())}
struct Body {
    n:BigUint,tape:Vec<char>,rotor:Point,initial:Point,
    stage:u64,bound:u64,primes:Vec<u64>,prime_index:usize,pending:u64,repeats:usize,
    frame:FixedQuquartSic,dual:PreparedSicDual,preparation:Value,
    events:Vec<Value>,reentries:Vec<Value>,reentry_state:u32,learning_tokens:Vec<u16>,word:Vec<u64>,result:Option<Value>,
    deadline:Option<Instant>,exhausted:bool,error:Option<String>,json:CString,seconds:f64,
}
impl Body {
    fn expired(&mut self)->bool{
        if self.deadline.is_some_and(|d|Instant::now()>=d){self.exhausted=true;}self.exhausted
    }
    fn prime(&mut self)->u64{
        if let Some(&p)=self.primes.get(self.prime_index){self.prime_index+=1;return p;}
        let mut c=self.primes.last().map_or(2,|p|if *p==2{3}else{p+2});
        loop{
            if self.primes.iter().take_while(|&&p|p<=c/p).all(|p|c%p!=0){
                self.primes.push(c);self.prime_index+=1;return c;
            }
            c+=2;
        }
    }
    fn new_stage(&mut self)->Result<Value,String>{
        self.stage+=1;self.bound=self.bound.checked_mul(2).ok_or("prime winding stage extent overflow")?;
        self.prime_index=0;self.pending=0;self.repeats=0;self.word.clear();
        // The first carrier is the squared native (-1+4i)/sqrt(17).
        // Subsequent integer angular charts retain the same norm-one torus.
        let t=BigUint::from(4+self.stage);let square=&t*&t;
        self.rotor=[subtract(&BigUint::one(),&(&square%&self.n),&self.n),
            (&t*2u8)%&self.n,(&square+1u8)%&self.n];
        let conjugated=self.reentry_state&4!=0;
        if conjugated{self.rotor[1]=subtract(&BigUint::zero(),&self.rotor[1],&self.n);}
        Ok(json!({"stage":self.stage,"bound":self.bound,"chart_parameter":t.to_string(),"point":point(&self.rotor),
            "reentry_state":self.reentry_state,"chirality_conjugated":conjugated}))
    }
    fn read(&self,p:&Point)->Result<(Option<BigUint>,Value),String>{
        if !norm(p,&self.n){return Err("prime braid lost torus norm".into());}
        let n=&self.n;let half=(n+1u8)/2u8;
        let direction=[&p[0]*&p[2]%n,&p[1]*&p[2]%n,BigUint::zero()];
        let normal=[&p[0]*&p[0]%n,&p[0]*&p[1]%n,&p[1]*&p[2]%n];
        let plus:Point=core::array::from_fn(|i|(&normal[i]+&direction[i])%n);
        let minus:Point=core::array::from_fn(|i|subtract(&normal[i],&direction[i],n));
        let returned:Point=core::array::from_fn(|i|subtract(&plus[i],&minus[i],n)*&half%n);
        let restored_normal:Point=core::array::from_fn(|i|(&plus[i]+&minus[i])*&half%n);
        if returned!=direction||restored_normal!=normal{return Err("sphere inner return changed its source address".into());}
        let z2=&p[2]*&p[2]%n;
        let amplitudes=[FixedComplex{re:BigInt::from(subtract(&returned[0],&z2,n)),im:BigInt::zero()},
            FixedComplex{re:BigInt::zero(),im:BigInt::from(returned[1].clone())},
            FixedComplex{re:BigInt::from(z2),im:BigInt::zero()},
            FixedComplex{re:BigInt::one(),im:BigInt::zero()}];
        let g: [(BigInt,BigInt);16]=gram(&amplitudes).try_into().unwrap();
        let masses=self.frame.gram_mass_numerators(&g)?;
        let recovered=self.dual.apply(&self.frame,&masses)?;
        for (actual,back) in g.iter().zip(&recovered.numerators){
            if &actual.0*&recovered.denominator!=back.0||&actual.1*&recovered.denominator!=back.1{
                return Err("full SIC dual lost a torus coordinate".into());
            }
        }
        // Every divisor witness is read from the reconstructed Gram, not
        // from an independently invoked factor producer or candidate lane.
        let decode=|v:&BigInt|->Result<BigUint,String>{
            if v%&recovered.denominator!=BigInt::zero(){return Err("SIC readout denominator is open".into());}
            (v/&recovered.denominator).to_biguint().ok_or("negative SIC winding coordinate".into())
        };
        let chord=decode(&recovered.numerators[3].0)?;
        let sine=decode(&(-&recovered.numerators[7].1))?;
        let denominator=decode(&recovered.numerators[11].0)?;
        let witnesses=[chord.clone(),sine.clone(),(&chord+2u8*&denominator)%n,denominator];
        let divisors:Vec<_>=witnesses.iter().map(|v|gcd(v.clone(),n.clone())).collect();
        let found=divisors.iter().find(|d|**d>BigUint::one()&&*d<n).cloned();
        let frames=[("horn",2u8),("spindle",1u8),("sphere",0u8)].into_iter().map(|(name,r)|{
            let outer:Point=core::array::from_fn(|i|(&direction[i]*r+&normal[i]*2u8)%n);
            json!({"name":name,"R":r,"r":2,"point":point(&outer)})
        }).collect::<Vec<_>>();
        Ok((found,json!({"point":point(p),"norm_verified":true,"direction":point(&direction),"normal":point(&normal),
            "frames":frames,"sphere_inner_plus":point(&plus),"sphere_inner_minus":point(&minus),
            "returned_direction":point(&returned),"restored_normal":point(&restored_normal),
            "amplitudes":amplitudes.iter().map(|z|[z.re.to_string(),z.im.to_string()]).collect::<Vec<_>>(),
            "gram":coords(&g),"mass_numerators":masses.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "dual_numerators":coords(&recovered.numerators),"dual_denominator":recovered.denominator.to_string(),
            "witnesses":witnesses.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "gcds":divisors.iter().map(ToString::to_string).collect::<Vec<_>>(),"exact_sic_return":true})))
    }
    fn close(&mut self,d:BigUint)->Result<(),String>{
        if d<=BigUint::one()||d>=self.n||&self.n%&d!=BigUint::zero(){return Err("SIC did not emit a proper divisor".into());}
        let q=&self.n/&d;let p_tape=mf::decimal_to_tape(&d.to_string()).unwrap();let q_tape=mf::decimal_to_tape(&q.to_string()).unwrap();
        if mf::mul(&p_tape,&q_tape)!=self.tape{return Err("prime torus factor words do not close N".into());}
        self.result=Some(json!({"p":d.to_string(),"q":q.to_string(),"remainder":"0","product":self.n.to_string(),
            "p_word":mf::emit_numeral(&p_tape),"q_word":mf::emit_numeral(&q_tape),
            "producer":"prime-torus-sic","exact_product":true,"paired_boundary":true}));Ok(())
    }
    fn advance(&mut self,port:usize)->Result<(),String>{
        if self.expired()||self.result.is_some(){return Ok(());}
        let started=Instant::now();let before=self.rotor.clone();let mut word=Vec::new();let mut changes=Vec::new();
        let mut points=Vec::new();let mut stage_terminals=Vec::new();let mut divisor=None;
        for _ in 0..64 {
            if self.expired(){break;}
            if self.repeats==0 {
                let p=self.prime();
                if p>self.bound{
                    let (d,r)=self.read(&self.rotor)?;
                    stage_terminals.push(json!({"offset":word.len(),"stage":self.stage,"bound":self.bound,"readout":r}));
                    if d.is_some(){divisor=d;break;}
                    let mut change=self.new_stage()?;change["offset"]=json!(word.len());changes.push(change);continue;
                }
                let mut v=p;self.repeats=1;
                while v<=self.bound/p{v*=p;self.repeats+=1;}
                self.pending=p;
            }
            self.rotor=power(&self.rotor,self.pending,&self.n);self.repeats-=1;
            if !norm(&self.rotor,&self.n){return Err("prime winding changed source norm".into());}
            self.word.push(self.pending);word.push(self.pending);points.push(self.rotor.clone());
        }
        let (terminal_divisor,readout)=self.read(&self.rotor)?;
        if divisor.is_none(){divisor=terminal_divisor;}let mut cuts=Vec::new();
        // Retain and examine the actual prefix points if a batch crosses a
        // divisor boundary before its terminal point. No factor proposals.
        if divisor.is_none()&&readout["gcds"].as_array().unwrap().iter().any(|d|d.as_str()==Some(&self.n.to_string())){
            for (at,p) in points.iter().enumerate(){
                let (d,r)=self.read(p)?;cuts.push(json!({"prefix":at+1,"readout":r}));
                if d.is_some(){divisor=d;break;}
            }
        }
        if let Some(d)=divisor{self.close(d)?;}
        self.events.push(json!({"port":port,"seconds":started.elapsed().as_secs_f64(),"before":point(&before),
            "after":point(&self.rotor),"prime_word":word,"stage_changes":changes,"stage":self.stage,"bound":self.bound,
            "sic_readout":readout,"prefix_readouts":cuts,"stage_terminals":stage_terminals,
            "reentry_state":self.reentry_state,"reentry_count":self.reentries.len(),
            "pending_prime":self.pending,"pending_repetitions":self.repeats,"produced":self.result.is_some()}));Ok(())
    }
    fn update_context(&mut self,port:usize){
        let mut values=vec![("source",self.n.clone()),("torus_x",self.rotor[0].clone()),
            ("torus_y",self.rotor[1].clone()),("torus_z",self.rotor[2].clone())];
        for (name,value) in [("stage",self.stage),("bound",self.bound),("reentry_mask",self.reentry_state as u64),
            ("pending_prime",self.pending),("pending_repetitions",self.repeats as u64)]{
            values.push((name,BigUint::from(value)));
        }
        let mut tokens=vec![256,85,(port%3) as u16];let mut fields=Vec::new();
        for (id,(name,value)) in values.iter().enumerate(){
            let width=value.bits().max(1) as usize;
            let cells:Vec<_>=(0..width).map(|i|if value.bit(i as u64){"T"}else{"F"}).collect();
            tokens.push(id as u16);tokens.extend((width as u64).to_le_bytes().iter().map(|v|*v as u16));
            for pair in cells.chunks(2){
                let mut packed=0u16;
                for (j,cell) in pair.iter().enumerate(){packed|=(if *cell=="T"{1}else{2})<<(2*j);}
                tokens.push(266+packed);
            }
            fields.push(json!({"name":name,"word":{"numeral":value.to_string(),"cells":cells}}));
        }
        tokens.push(257);self.learning_tokens=tokens;
        if let Some(event)=self.events.last_mut(){event["learning_context"]=json!({
            "schema":"prime-torus-learning-context-v1","arm":port%3,"fields":fields});}
    }
    fn snapshot(&mut self)->*const c_char{
        self.json=CString::new(json!({"schema":"prime-torus-sic-v2","input_boundary":"N alone",
            "source":self.n.to_string(),"source_word":mf::emit_numeral(&self.tape),"construction":"prime-torus-sic",
            "allowed_operations":["prime-braid-windings","horn-spindle-sphere-inner-return","full-SIC-dual"],
            "preparation_seconds":self.seconds,"preparation":self.preparation,"initial_point":point(&self.initial),
            "operations":self.events,"retained_prime_word":self.word,"point":point(&self.rotor),
            "stage":self.stage,"bound":self.bound,"next_prime_index":self.prime_index,
            "pending_prime":self.pending,"pending_repetitions":self.repeats,"logical_reentry":self.reentries,
            "reentry_state":self.reentry_state,"learning_tokens":self.learning_tokens,
            "result":self.result,"budget_exhausted":self.exhausted,"error":self.error,
            "boundary":if self.result.is_some(){"closed"}else{"held"}}).to_string()).unwrap();self.json.as_ptr()
    }
}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_create(source:*const c_char)->*mut c_void{
    let result=std::panic::catch_unwind(||->Result<Body,String>{
        let start=Instant::now();let raw=CStr::from_ptr(source).to_str().map_err(|_|"source is not UTF8")?;
        let n:BigUint=raw.trim().parse().map_err(|_|"source is not an integer")?;
        if n.bits()<200||&n%2u8!=BigUint::one(){return Err("requires odd N of at least 200 bits".into());}
        let tape=mf::decimal_to_tape(&n.to_string()).unwrap();
        let format=FixedPointFormat::for_modulus_bits(n.bits())?;
        let frame=FixedQuquartSic::new(&format)?;let dual=frame.prepare_exact_dual()?;
        let preparation=json!({"fractional_bits":format.w_bits,
            "rays":frame.rays().iter().map(|r|r.iter().map(|z|[z.re.to_string(),z.im.to_string()]).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "source_rotor":"square of (-1+4i)/sqrt(17)","base": ["-15","-8","17"]});
        let rotor=[&n-15u8,&n-8u8,BigUint::from(17u8)];
        let deadline=std::env::var("ORGANISM_FACTOR_BUDGET_SECONDS").ok().and_then(|x|x.parse::<u64>().ok()).map(|s|Instant::now()+Duration::from_secs(s));
        Ok(Body{n,tape,initial:rotor.clone(),rotor,stage:0,bound:format.modulus_bits.saturating_mul(format.modulus_bits),
            primes:Vec::new(),prime_index:0,pending:0,repeats:0,frame,dual,preparation,
            events:Vec::new(),reentries:Vec::new(),reentry_state:0,learning_tokens:Vec::new(),word:Vec::new(),result:None,deadline,exhausted:false,error:None,
            json:CString::new("{}").unwrap(),seconds:start.elapsed().as_secs_f64()})
    });
    match result{Ok(Ok(b))=>Box::into_raw(Box::new(b)) as *mut c_void,_=>{eprintln!("restricted prime torus source preparation failed");std::ptr::null_mut()}}
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_destroy(p:*mut c_void){drop(Box::from_raw(p as *mut Body));}
#[no_mangle] pub extern "C" fn organism_factor_components()->usize{3}
#[no_mangle] pub unsafe extern "C" fn organism_factor_source_token(p:*mut c_void,i:usize)->i32{
    let b=&*(p as *mut Body);let bits:Vec<_>=b.tape.iter().rev().copied().collect();
    bits.chunks(4).nth(i).map_or(-1,|c|c.iter().fold(0,|a,x|a*2+i32::from(*x=='⊥')))
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_reentry(p:*mut c_void,a:u32,b:u32,c:u32,k:u32)->i32{
    let body=&mut*(p as *mut Body);if body.expired(){return 1;}
    if a>15||b>15||c>15||!matches!(k,1|2){return -1;}
    let permutation=((a&1)<<1)|((a&2)>>1)|((a&4)<<1)|((a&8)>>1);
    let next=if k==2 {(!( ((a&1)<<3)|((a&2)<<1)|((a&4)>>1)|((a&8)>>3) ))&15}
        else {(0..4).find(|i|a&(1<<i)==0).map_or(a,|i|a|(1<<i))};
    if a!=body.reentry_state||b!=permutation||c!=next||(k==2)!=(a==15){return -1;}
    let before=body.rotor.clone();let conjugated=(a&4)!=(c&4);
    if conjugated{body.rotor[1]=subtract(&BigUint::zero(),&body.rotor[1],&body.n);}
    body.reentry_state=c;
    body.reentries.push(json!({"before":a,"permuted":b,"after":c,"kind":k,
        "at_operation":body.events.len(),"conjugated":conjugated,
        "point_before":point(&before),"point_after":point(&body.rotor)}));0
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_advance(p:*mut c_void,port:usize)->i32{
    let body=&mut*(p as *mut Body);let before_count=body.events.len();let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String>{
        for _ in 0..64 {if body.expired()||body.result.is_some(){break;}body.advance(port)?;}
        Ok(())
    }));
    if body.events.len()>before_count{body.update_context(port);}
    match result{Ok(Ok(()))=>if body.result.is_some(){2}else{1},Ok(Err(e))=>{body.error=Some(e);body.exhausted=true;4},Err(_)=>{body.error=Some("prime torus operation panicked".into());body.exhausted=true;4}}
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_closed(p:*mut c_void)->bool{(*(p as *mut Body)).result.is_some()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_should_yield(p:*mut c_void)->bool{(&mut*(p as *mut Body)).expired()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_operation_count(p:*mut c_void)->usize{(*(p as *mut Body)).events.len()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_state_token(p:*mut c_void,i:usize)->i32{
    let body=&*(p as *mut Body);
    body.learning_tokens.get(i).map_or(-1,|v|*v as i32)
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_snapshot(p:*mut c_void)->*const c_char{(&mut*(p as *mut Body)).snapshot()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_observation(p:*mut c_void)->*const c_char{
    let b=&mut*(p as *mut Body);b.json=CString::new(json!({"source":b.n.to_string(),"operation":b.events.last()}).to_string()).unwrap();b.json.as_ptr()
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stage_terminal_and_reentry_context_on_source_200(){
        let path=std::env::var("PRIME_TORUS_TEST_SOURCE").expect("N-only 200-bit source path");
        let source=std::fs::read_to_string(path).unwrap();
        let text=CString::new(source.trim()).unwrap();
        let handle=unsafe{organism_factor_create(text.as_ptr())};assert!(!handle.is_null());
        let original=unsafe{(*(handle as *mut Body)).rotor.clone()};
        assert_eq!(unsafe{organism_factor_reentry(handle,0,0,1,1)},0);
        assert_eq!(unsafe{organism_factor_reentry(handle,1,2,3,1)},0);
        assert_eq!(unsafe{organism_factor_reentry(handle,3,3,7,1)},0);
        let token_length;
        {
            let body=unsafe{&mut*(handle as *mut Body)};assert!(body.n.bits()>=200);
            assert_eq!(body.reentry_state,7);assert_ne!(body.rotor,original);
            assert_eq!(body.rotor[0],original[0]);assert_eq!(body.rotor[2],original[2]);
            assert_eq!((&body.rotor[1]+&original[1])%&body.n,BigUint::zero());
            assert!(norm(&body.rotor,&body.n));
            // Isolate a stage boundary on the actual 200-bit N. This does
            // not use a small source or supply reference factors.
            let terminal=power(&body.rotor,2,&body.n);
            body.rotor=terminal.clone();body.word=vec![2];body.bound=2;
            body.primes=vec![2,3];body.prime_index=1;
            body.advance(0).unwrap();
            let event=&body.events[0];let boundary=&event["stage_terminals"][0];
            assert_eq!(boundary["offset"],0);assert_eq!(boundary["bound"],2);
            assert_eq!(boundary["readout"]["point"],point(&terminal));
            assert_eq!(event["stage_changes"][0]["offset"],0);
            assert_ne!(event["stage_changes"][0]["point"],point(&terminal));
            assert_eq!(body.n.to_string(),source.trim());
            body.update_context(0);token_length=body.learning_tokens.len();
            assert!(token_length>100);
            assert_eq!(body.events.last().unwrap()["learning_context"]["fields"][0]["word"]["numeral"],source.trim());
        }
        assert_eq!(unsafe{organism_factor_state_token(handle,0)},256);
        assert_eq!(unsafe{organism_factor_state_token(handle,token_length)},-1);
        unsafe{organism_factor_destroy(handle)};
    }
}
