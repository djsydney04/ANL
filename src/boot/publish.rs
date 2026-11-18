use super::Bundle;
use crate::bounded::OutputError;
use rustix::fs::{self, AtFlags, Dir, FileType, Mode, OFlags, RenameFlags};
use std::{
    collections::BTreeSet,
    fs::File,
    io::{Read, Write},
    path::Path,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
fn error(message: impl Into<String>) -> OutputError {
    OutputError::Infrastructure(message.into())
}
fn same(a: &fs::Stat, b: &fs::Stat) -> bool {
    a.st_dev == b.st_dev && a.st_ino == b.st_ino && a.st_mode == b.st_mode
}

pub(super) fn publish(bundle: &Bundle, destination: &Path) -> Result<(), OutputError> {
    let final_component = destination
        .as_os_str()
        .as_encoded_bytes()
        .rsplit(|b| *b == b'/')
        .next()
        .unwrap_or_default();
    if matches!(final_component, b"" | b"." | b"..") {
        return Err(error("boot output requires a directory basename"));
    }
    let basename = destination
        .file_name()
        .ok_or_else(|| error("boot output requires a directory basename"))?;
    let parent_path = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let parent = fs::open(
        parent_path,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|e| error(format!("cannot open boot output parent: {e}")))?;
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| error("cannot identify boot staging directory"))?
        .as_nanos();
    let mut staging = None;
    for _ in 0..100 {
        let name = format!(
            ".anl-boot-{}-{stamp}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        match fs::mkdirat(&parent, &name, Mode::RWXU) {
            Ok(()) => {
                staging = Some(name);
                break;
            }
            Err(rustix::io::Errno::EXIST) => {}
            Err(e) => return Err(error(format!("cannot create boot staging directory: {e}"))),
        }
    }
    let staging = staging.ok_or_else(|| error("cannot create a fresh boot staging directory"))?;
    let result = (|| -> Result<(), String> {
        let directory = fs::openat(
            &parent,
            &staging,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|e| e.to_string())?;
        let owned = fs::fstat(&directory).map_err(|e| e.to_string())?;
        let mut expected = BTreeSet::new();
        for (name, text) in &bundle.files {
            expected.insert(name.as_bytes().to_vec());
            let fd = fs::openat(
                &directory,
                *name,
                OFlags::RDWR | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                Mode::RUSR | Mode::WUSR,
            )
            .map_err(|e| e.to_string())?;
            let mut file = File::from(fd);
            file.write_all(text.as_bytes())
                .and_then(|()| file.flush())
                .map_err(|e| e.to_string())?;
        }
        let mut actual = BTreeSet::new();
        for entry in Dir::read_from(&directory).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let name = entry.file_name().to_bytes();
            if name != b"." && name != b".." {
                actual.insert(name.to_vec());
            }
        }
        if expected != actual {
            return Err("boot staging inventory changed".into());
        }
        for (name, text) in &bundle.files {
            let fd = fs::openat(
                &directory,
                *name,
                OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                Mode::empty(),
            )
            .map_err(|e| e.to_string())?;
            let before = fs::fstat(&fd).map_err(|e| e.to_string())?;
            if FileType::from_raw_mode(before.st_mode) != FileType::RegularFile
                || before.st_size < 0
                || before.st_size as u64 != text.len() as u64
            {
                return Err("boot staging file changed".into());
            }
            let mut file = File::from(fd);
            let mut bytes = Vec::new();
            Read::by_ref(&mut file)
                .take(text.len() as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(|e| e.to_string())?;
            let after = fs::fstat(&file).map_err(|e| e.to_string())?;
            let named = fs::statat(&directory, *name, AtFlags::SYMLINK_NOFOLLOW)
                .map_err(|e| e.to_string())?;
            if bytes != text.as_bytes() || !same(&before, &after) || !same(&after, &named) {
                return Err("boot staging file changed".into());
            }
        }
        let current = fs::fstat(&directory).map_err(|e| e.to_string())?;
        let named =
            fs::statat(&parent, &staging, AtFlags::SYMLINK_NOFOLLOW).map_err(|e| e.to_string())?;
        if !same(&owned, &current) || !same(&current, &named) {
            return Err("boot staging directory changed".into());
        }
        fs::renameat_with(&parent, &staging, &parent, basename, RenameFlags::NOREPLACE)
            .map_err(|e| e.to_string())?;
        Ok(())
    })();
    result.map_err(|e| {
        error(format!(
            "cannot publish boot output; staging {staging} retained: {e}"
        ))
    })
}
