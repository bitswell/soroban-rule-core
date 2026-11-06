use cedar_to_rule_core::{Bindings, compile};
use std::{fs::File, io::Read, process::ExitCode};
fn read_limited(path: &str, max: u64) -> Result<String, Box<dyn std::error::Error>> {
    let mut text = String::new();
    File::open(path)?.take(max + 1).read_to_string(&mut text)?;
    if text.len() as u64 > max {
        return Err(format!("{path}: input exceeds {max} bytes").into());
    }
    Ok(text)
}
fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 2 {
        return Err("usage: cedar-to-rule-core POLICY.cedar BINDINGS.json".into());
    }
    let source = read_limited(&args[0], 16_384)?;
    let bindings = Bindings::from_json(&read_limited(&args[1], 65_536)?)?;
    let compiled = compile(&source, bindings)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&compiled.emitted_json())?
    );
    Ok(())
}
fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("cedar-to-rule-core: {e}");
            ExitCode::FAILURE
        }
    }
}
