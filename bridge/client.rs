// Shared hosted client. The evaluator and certificates live in Lean.
use std::path::PathBuf;
use std::process::Command;
use std::io::Write;

pub fn run(args: &[String]) -> i32 {
    run_to(args, |bytes| { let _ = std::io::stdout().lock().write_all(bytes); })
}

pub fn run_to(args: &[String], emit: impl FnOnce(&[u8])) -> i32 {
    if args.is_empty() || matches!(args[0].as_str(), "help" | "--help" | "-h") {
        emit(b"reentry [orbit SEED TICK] identity|negation|hold|seeded MASK|constant MASK|Y MASK|OP MASK\nreentry [orbit SEED TICK] program TOKEN ... (@ applies the two preceding terms)\nreentry word GLYPHS [SEED TICK]\nreentry table SEED TICK OUTPUT0 ... OUTPUT15\nOP: join_i meet_i join_t meet_t join_f meet_f; native mask bits: N=1 T=2 F=4 B=8\n");
        return 0;
    }
    let mut command = match evaluator() {
        Ok(command) => command,
        Err(error) => { eprintln!("Lean kernel bridge: {error}"); return 2; }
    };
    match command.args(args).output() {
        Ok(output) => {
            emit(&output.stdout);
            if !output.status.success() { let _ = std::io::stderr().lock().write_all(&output.stderr); }
            output.status.code().unwrap_or(2)
        },
        Err(error) => { eprintln!("Lean kernel bridge: {error}"); 2 }
    }
}

fn evaluator() -> Result<Command, String> {
    let root = std::env::var_os("P4RAKERNEL_ROOT").map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../p4rakernel"));
    let compiler_dir = root.join("build/stage1/bin");
    let mut paths = vec![compiler_dir.clone()];
    if let Some(path) = std::env::var_os("PATH") { paths.extend(std::env::split_paths(&path)); }
    let path = std::env::join_paths(paths).map_err(|error| error.to_string())?;
    let mut command = Command::new(compiler_dir.join("lake"));
    command.current_dir(root.join("p4ramill"))
        .env("PATH", path)
        .args(["env", "lean", "--run", "KernelBridge.lean"]);
    Ok(command)
}

/// Hosted admission requires the actual Lean carrier and certified Y reducer.
pub fn ensure_default() -> Result<(), String> {
    static READY: std::sync::OnceLock<Result<(), String>> = std::sync::OnceLock::new();
    READY.get_or_init(|| {
        let output = evaluator()?.args(["Y", "6"]).output().map_err(|e| e.to_string())?;
        let report = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
        if !output.status.success() {
            return Err(String::from_utf8_lossy(&output.stderr).into_owned());
        }
        if !report.lines().any(|line| line == "backend=Lean-kernel SIXTEEN_3=active mask-order=N,T,F,B")
            || !report.lines().any(|line| line == "kernel-reentry=6")
            || !report.lines().any(|line| line == "least=6 greatest=6 certified=true") {
            return Err("Lean did not certify kernel re-entry and the default recursive carrier".into());
        }
        Ok(())
    }).clone()
}

pub fn run_word(args: &[String], table: impl FnOnce(&str) -> Result<[u8; 16], String>) -> i32 {
    run_word_to(args, table, |bytes| { let _ = std::io::stdout().lock().write_all(bytes); })
}

pub fn run_word_to(args: &[String], table: impl FnOnce(&str) -> Result<[u8; 16], String>, emit: impl FnOnce(&[u8])) -> i32 {
    if args.len() != 2 && args.len() != 4 {
        eprintln!("reentry word GLYPHS [SEED TICK]"); return 2;
    }
    let map = match table(&args[1]) {
        Ok(map) => map,
        Err(error) => { eprintln!("phase word: {error}"); return 2; }
    };
    let mut request = vec!["table".to_owned(), args.get(2).cloned().unwrap_or_else(|| "0".into()),
        args.get(3).cloned().unwrap_or_else(|| "4".into())];
    request.extend(map.into_iter().map(|value| value.to_string()));
    run_to(&request, emit)
}
