//! Validation transport to the production MIR reader.
use std::{
    env,
    fs::File,
    io::{self, Read, Write},
    process::ExitCode,
};

fn report(text: &str, code: u8) -> ExitCode {
    let mut stdout = match nix::unistd::dup(io::stdout()) {
        Ok(fd) => File::from(fd),
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "output_io_error: {error}");
            return ExitCode::from(4);
        }
    };
    match stdout
        .write_all(text.as_bytes())
        .and_then(|()| stdout.flush())
    {
        Ok(()) => ExitCode::from(code),
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "output_io_error: {error}");
            ExitCode::from(4)
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<_> = env::args_os().skip(1).collect();
    if args.len() != 1 {
        return ExitCode::from(4);
    }
    let mut bytes = Vec::new();
    let input = File::open(&args[0]).and_then(|file| file.take(8_388_609).read_to_end(&mut bytes));
    if let Err(error) = input {
        eprintln!("{error}");
        return ExitCode::from(4);
    }
    if bytes.len() > 8_388_608 {
        eprintln!("MIR input byte limit exceeded");
        return report("resource_limit\n", 3);
    }
    let text = match String::from_utf8(bytes) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("{error}");
            return report("invalid_ir\n", 1);
        }
    };
    match anl::memory_evidence::validate_mir(&text) {
        Ok(()) => report("accepted\n", 0),
        Err(error) => {
            eprintln!("{error}");
            match error {
                anl::core::ImportError::Invalid(_) => report("invalid_ir\n", 1),
                anl::core::ImportError::ResourceLimit(_) => report("resource_limit\n", 3),
            }
        }
    }
}
