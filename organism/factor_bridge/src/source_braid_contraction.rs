//! Organism transport for one retained source-braid coefficient computation.
use std::ffi::{c_char,c_void,CStr,CString};
use std::time::{Instant,Duration};
use serde_json::json;
use g_momonados::{source_braid_contraction::SourceBraidContraction,word_tape::WordTape};
use vox::morphism_factor as mf;
struct Body {source:Vec<char>,engine:SourceBraidContraction,deadline:Option<Instant>,json:CString,tokens:Vec<u16>,preparation_seconds:f64}
impl Body {
    fn expired(&mut self)->bool{if self.deadline.is_some_and(|d|Instant::now()>=d){self.engine.exhausted=true;}self.engine.exhausted}
    fn context(&mut self,port:usize){
        let values=self.engine.context_values();let mut tokens=vec![256,85,(port%3) as u16];let mut fields=Vec::new();
        for (id,(name,word)) in values.iter().enumerate(){
            let width=word.bit_len().max(1);let cells:Vec<_>=(0..width).map(|i|if word.bit_at(i){"T"}else{"F"}).collect();
            tokens.push(id as u16);tokens.extend((width as u64).to_le_bytes().iter().map(|v|*v as u16));
            for pair in cells.chunks(2){let mut packed=0u16;for(j,c)in pair.iter().enumerate(){packed|=(if *c=="T"{1}else{2})<<(2*j);}tokens.push(266+packed);}
            fields.push(json!({"name":name,"word":{"numeral":mf::dec_of(&word.to_imasm_tape()),"cells":cells}}));
        }
        tokens.push(257);self.tokens=tokens;
        if let Some(event)=self.engine.events.last_mut(){event["learning_context"]=json!({"schema":"source-braid-learning-context-v1","arm":port%3,"fields":fields});}
    }
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_create(source:*const c_char)->*mut c_void{
    let started=Instant::now();
    let result=std::panic::catch_unwind(||->Result<Body,String>{
        let raw=CStr::from_ptr(source).to_str().map_err(|_|"source UTF8")?;
        let cells=mf::decimal_to_tape(raw.trim()).ok_or("N-only decimal source")?;
        if cells.len()<2{return Err("source-braid execution requires a non-unit source".into());}
        let word=WordTape::from_imasm_tape(&cells).ok_or("native source tape")?;
        let directory=std::env::var("ORGANISM_FACTOR_RETAINED_DIR").map_err(|_|"runner must supply the retained output directory")?;
        let deadline=std::env::var("ORGANISM_FACTOR_BUDGET_SECONDS").ok().and_then(|s|s.parse::<u64>().ok()).map(|s|started+Duration::from_secs(s));
        let engine=SourceBraidContraction::prepare(word,std::path::Path::new(&directory))?;
        Ok(Body{source:cells,engine,deadline,json:CString::new("{}").unwrap(),tokens:Vec::new(),preparation_seconds:started.elapsed().as_secs_f64()})
    });
    match result{Ok(Ok(b))=>Box::into_raw(Box::new(b))as*mut c_void,other=>{
        eprintln!("source-braid preparation rejected: {}",match other{Ok(Err(e))=>e,_=>"native panic".into()});std::ptr::null_mut()}}
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_destroy(p:*mut c_void){drop(Box::from_raw(p as*mut Body));}
#[no_mangle] pub extern "C" fn organism_factor_components()->usize{3}
#[no_mangle] pub unsafe extern "C" fn organism_factor_source_token(p:*mut c_void,i:usize)->i32{
    let b=&*(p as*mut Body);let cells:Vec<_>=b.source.iter().rev().collect();cells.chunks(4).nth(i).map_or(-1,|c|c.iter().fold(0,|v,m|2*v+i32::from(**m=='⊥')))
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_reentry(p:*mut c_void,a:u32,b:u32,c:u32,k:u32)->i32{
    let body=&mut*(p as*mut Body);if body.expired(){return 1;}
    match body.engine.reenter(a,b,c,k){Ok(())=>0,Err(e)=>{body.engine.error=Some(e);-1}}
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_advance(p:*mut c_void,port:usize)->i32{
    let body=&mut*(p as*mut Body);if body.expired(){return 1;}
    let before=body.engine.events.len();
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||body.engine.advance(port,body.deadline)));
    if result.is_err(){body.engine.error=Some("source-braid coefficient operation panicked".into());}
    if body.engine.events.len()>before{body.context(port);}
    if body.engine.result.is_some(){2}else if body.engine.error.is_some(){4}else{1}
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_closed(p:*mut c_void)->bool{(*(p as*mut Body)).engine.result.is_some()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_should_yield(p:*mut c_void)->bool{let b=&mut*(p as*mut Body);b.expired()||b.engine.error.is_some()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_operation_count(p:*mut c_void)->usize{(*(p as*mut Body)).engine.events.len()}
#[no_mangle] pub unsafe extern "C" fn organism_factor_state_token(p:*mut c_void,i:usize)->i32{let b=&*(p as*mut Body);b.tokens.get(i).map_or(-1,|v|*v as i32)}
#[no_mangle] pub unsafe extern "C" fn organism_factor_snapshot(p:*mut c_void)->*const c_char{
    let b=&mut*(p as*mut Body);let mut snapshot=b.engine.snapshot().unwrap_or_else(|e|json!({"error":e}));
    snapshot["preparation_seconds"]=json!(b.preparation_seconds);
    b.json=CString::new(snapshot.to_string()).unwrap();b.json.as_ptr()
}
#[no_mangle] pub unsafe extern "C" fn organism_factor_observation(p:*mut c_void)->*const c_char{
    let b=&mut*(p as*mut Body);b.json=CString::new(json!({"source":mf::dec_of(&b.source),"operation":b.engine.events.last()}).to_string()).unwrap();b.json.as_ptr()
}
