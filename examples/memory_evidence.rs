use std::{env, path::Path, process::ExitCode};
fn main() -> ExitCode {
    let args: Vec<_> = env::args_os().skip(1).collect();
    let result = match args.as_slice() {
        [source, destination] => {
            anl::memory_evidence::export_bundle(Path::new(source), Path::new(destination))
        }
        [mode, core, destination] if mode == "--core" => {
            anl::memory_evidence::export_core_bundle(Path::new(core), Path::new(destination))
        }
        _ => {
            eprintln!(
                "usage: memory_evidence FILE OUT_DIR | memory_evidence --core CORE_JSON OUT_DIR"
            );
            return ExitCode::from(4);
        }
    };
    match result {
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
