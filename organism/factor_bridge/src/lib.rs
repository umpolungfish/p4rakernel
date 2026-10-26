use std::ffi::{c_char, c_void, CStr, CString};
use std::time::{Instant,Duration};
use serde_json::{json, Value};
use vox::{factor_synthesis::{FactorSynthesis, FactorReturn}, glut_system::{FoldStats, PreparedGlutMembrane}, morphism_factor as mf};
use vox::toroidal_division as torus;

struct Body {
    source: Vec<char>,
    resident: FactorSynthesis,
    returned: Option<FactorReturn>,
    events: Vec<Value>,
    json: CString,
    preparation: f64,
    identity: Option<usize>,
    error: Option<String>,
    deadline: Option<Instant>,
    budget_exhausted: bool,
}
fn stats(s: &FoldStats) -> Value {
    json!({"dialectic_descents":s.dialectic_descents,"dialectic_contractions":s.dialectic_contractions,
        "square_advances":s.square_advances,"square_cells":s.square_cells,"phase_columns":s.phase_columns,
        "phase_rows":s.phase_rows,"phase_partials":s.phase_partials,"phase_stage":s.phase_stage.to_string(),
        "correlation_work":s.correlation_work,"correlation_decisions":s.correlation_decisions,
        "correlation_conflicts":s.correlation_conflicts,"mask_work":s.mask_work,
        "support_forced":s.support_forced,"support_rejected":s.support_rejected,
        "decisions":s.decisions,"frontier":s.frontier,"producing_port":s.producing_port,
        "catalyst_turns":s.catalyst_turns,"conditioned_bindings":s.conditioned_bindings,
        "conditioned_windows":s.conditioned_windows,"catalyst_inverse_returned":s.catalyst_inverse_returned})
}
impl Body {
    fn snapshot(&mut self) -> *const c_char {
        let result = self.returned.as_ref().map(|r| {
            let (q, remainder) = mf::divmod(&self.source, &r.p);
            let product = mf::mul(&r.p, &q);
            let (bank_p, bank_q) = (r.p.clone(), q.clone());
            let banked = r.membrane.as_ref().and_then(|m|m.retained_readout());
            let banked_closed = banked.as_ref().is_some_and(|read| read.exposed==0
                && !read.surviving.is_empty()
                && read.surviving.iter().all(|d|Some(d.observation)==self.identity));
            json!({"p":mf::dec_of(&r.p),"q":mf::dec_of(&q),"p_word":mf::emit_numeral(&r.p),
                "q_word":mf::emit_numeral(&q),"remainder":mf::dec_of(&remainder),
                "product":mf::dec_of(&product),"exact_product":product==self.source,
                "paired_boundary":q==r.q && mf::mul(&bank_p,&bank_q)==self.source && banked_closed,
                "banked_return":banked.as_ref().map(|b|json!({"exposed":b.exposed,
                    "deposits":b.deposits,"cleared":b.cleared,"restored":b.restored,
                    "surviving":b.surviving.len(),"same_resident":banked_closed})),
                "producer":r.producer,"actual_producing_port":self.resident.resident_stats().producing_port,
                "powerset_monad_laws":r.powerset_monad_laws_verified,
                "inverse_returned":r.catalyst_inverse_returned,
                "native_resident_retained":r.membrane.is_some(),
                "braid_dots":r.braid_dots.iter().map(|d|json!({"reentry":d.reentry,
                    "p":mf::dec_of(&d.p_value),"q":mf::dec_of(&d.q_value),
                    "source":mf::dec_of(&d.source_value),"product_closed":d.product_closed})).collect::<Vec<_>>()})
        });
        let report = json!({"schema":"organism-resident-factor-v1","input_boundary":"N alone",
            "source":mf::dec_of(&self.source),"source_word":mf::emit_numeral(&self.source),
            "preparation_seconds":self.preparation,"component_names":torus::OPERATIONS,
            "toroidal_division":self.resident.toroidal_snapshot(),
            "budget_exhausted":self.budget_exhausted,
            "toroidal_cell_decisions":self.resident.toroidal_decisions().iter().map(|d|
                json!({"cell":d.cell,"preference":d.preference.name(),"selected":d.selected.name(),
                    "evidence":d.evidence.name(),"hypothesis":d.hypothesis})).collect::<Vec<_>>(),
            "stats":stats(&self.resident.resident_stats()),"result":result,"operations":self.events,
            "resident_identity":self.identity,"error":self.error,
            "boundary":if self.returned.is_some(){"closed"}else{"held"}});
        self.json = CString::new(report.to_string()).unwrap();
        self.json.as_ptr()
    }
}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_create(source: *const c_char) -> *mut c_void {
    let outcome = std::panic::catch_unwind(|| -> Result<Body,String> {
        let started = Instant::now();
        let raw = CStr::from_ptr(source).to_str().map_err(|_|"invalid source")?;
        let tape = mf::decimal_to_tape(raw.trim()).ok_or("invalid N-only decimal")?;
        if tape.len()<128 || tape.first()!=Some(&'⊥') {return Err("requires odd N of at least128bits".into());}
        let mut resident = FactorSynthesis::new(&tape)?;
        resident.prepare_toroidal_division()?;
        let identity=resident.resident_identity();
        let deadline=std::env::var("ORGANISM_FACTOR_BUDGET_SECONDS").ok()
            .and_then(|s|s.parse::<u64>().ok()).map(|s|Instant::now()+Duration::from_secs(s));
        Ok(Body {source:tape,resident,returned:None,events:Vec::new(),json:CString::new("{}").unwrap(),
            preparation:started.elapsed().as_secs_f64(),identity,error:None,deadline,budget_exhausted:false})
    });
    match outcome {Ok(Ok(body))=>Box::into_raw(Box::new(body)) as *mut c_void,
        other=>{eprintln!("organism factor preparation rejected: {}", match other {Ok(Err(e))=>e,_=>"native panic".into()});std::ptr::null_mut()}}
}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_destroy(body:*mut c_void) {drop(Box::from_raw(body as *mut Body));}
#[no_mangle]
pub extern "C" fn organism_factor_components()->usize {torus::OPERATIONS.len()}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_source_token(body:*mut c_void,index:usize)->i32 {
    let body=&*(body as *mut Body);
    let big:Vec<_>=body.source.iter().rev().copied().collect();
    match big.chunks(4).nth(index) {Some(chunk)=>chunk.iter().fold(0,|n,c|2*n+i32::from(*c=='⊥')),None=>-1}
}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_advance(body:*mut c_void,port:usize)->i32 {
    let body=&mut*(body as *mut Body);
    if body.returned.is_some(){return 2;}
    if body.deadline.is_some_and(|d|Instant::now()>=d) {
        body.budget_exhausted=true;
        return 1;
    }
    let before=body.resident.resident_stats();let started=Instant::now();
    let mut torus_event=Value::Null;
    let mut torus_feedback=vox::belnap::B4::N;
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<Option<FactorReturn>,String> {
        let (returned,event,evidence)=body.resident.advance_toroidal_division(port)?;
        torus_event=event;
        torus_feedback=evidence;
        Ok(returned)
    }));
    match result {
        Ok(Ok(value))=>body.returned=value,
        Ok(Err(error))=>body.error=Some(error),
        Err(_)=>body.error=Some("native operation panic retained".into()),
    }
    let after=body.resident.resident_stats();
    if body.identity!=body.resident.resident_identity(){body.error=Some("factor resident identity changed".into());}
    let before_json=stats(&before);let after_json=stats(&after);
    let changed=before_json!=after_json;
    let conflict=after.correlation_conflicts>before.correlation_conflicts || body.error.is_some();
    let produced=body.returned.is_some();
    if let Some(r)=&body.returned {body.identity=r.membrane.as_ref().map(|m|m.resident_identity());}
    body.events.push(json!({"port":port,"toroidal_operation":torus_event,
        "executed_components":PreparedGlutMembrane::component_names(),
        "seconds":started.elapsed().as_secs_f64(),"before":before_json,
        "after":after_json,"changed":changed,"conflict":conflict,"produced":produced}));
    use vox::belnap::B4;
    let mut feedback=torus_feedback;
    if changed || produced {feedback=feedback.join(B4::T);}
    if conflict {feedback=feedback.join(B4::F);}
    if let Some(event)=body.events.last_mut(){event["feedback"]=json!(feedback.name());}
    match feedback {B4::N=>1,B4::T=>2,B4::F=>4,B4::B=>8}
}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_closed(body:*mut c_void)->bool {(*(body as *mut Body)).returned.is_some()}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_snapshot(body:*mut c_void)->*const c_char {(&mut*(body as *mut Body)).snapshot()}
#[no_mangle]
pub unsafe extern "C" fn organism_factor_observation(body:*mut c_void)->*const c_char {
    let body=&mut*(body as *mut Body);
    body.json=CString::new(json!({"source":mf::dec_of(&body.source),"operation":body.events.last(),
        "budget_exhausted":body.budget_exhausted}).to_string()).unwrap();
    body.json.as_ptr()
}

#[cfg(test)]
mod tests {
    use super::*;
    use vox::{belnap::B4,belnap_word::BelnapWord};
    #[test]
    fn native_source_survives_zero_carry_at_full_word_boundaries() {
        for width in [128,192,256,512] {
            let mut cells=vec![B4::T;width];cells[0]=B4::F;
            let value=BelnapWord::new(cells);
            let zero=BelnapWord::new(Vec::new());
            assert_eq!(value.add(&zero),value);
            assert_eq!(zero.add(&value),value);
            let (back,borrow)=value.add(&BelnapWord::new(vec![B4::T])).subtract(&BelnapWord::new(vec![B4::T]));
            assert_eq!(back,value);assert_eq!(borrow,B4::F);
        }
        let source="211060082272597355141159798675733025589";
        let tape=mf::decimal_to_tape(source).unwrap();
        assert_eq!(tape.len(),128);assert_eq!(mf::dec_of(&tape),source);
    }
}
