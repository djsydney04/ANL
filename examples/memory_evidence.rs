use std::{env, path::Path, process::ExitCode};
fn main() -> ExitCode {
    let args: Vec<_> = env::args_os().skip(1).collect();
    if args.len() != 2 {
        eprintln!("usage: memory_evidence FILE OUT_DIR");
        return ExitCode::from(4);
    }
    match anl::memory_evidence::export_bundle(Path::new(&args[0]), Path::new(&args[1])) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(
                if matches!(e, anl::bounded::OutputError::ResourceLimit(_)) {
                    3
                } else {
                    4
                },
            )
        }
    }
}
