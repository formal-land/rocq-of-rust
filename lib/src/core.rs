use crate::top_level::*;
use std::collections::{BTreeMap, HashMap};
use std::io;
use std::path::{Path, PathBuf};
use std::{fs, path, process, str};

/// CLI options
pub struct CliOptions {
    pub path: path::PathBuf,
    pub output: path::PathBuf,
    pub axiomatize: bool,
}

pub const LINE_WIDTH: usize = 80;

fn change_to_rocq_extension(path: &path::Path) -> PathBuf {
    let mut new_path = path.to_path_buf();
    new_path.set_extension("v");
    new_path
}

/// Write the content to a file only if it changed. This optimization is useful
/// in order not to force the `make` command to rebuild files that did not
/// change.
pub(crate) fn write_if_changed<P: AsRef<path::Path>, C: AsRef<[u8]>>(
    path: P,
    new_content: C,
) -> std::io::Result<()> {
    let path = path.as_ref();
    let new_content = new_content.as_ref();

    // If the file does not exist, or if the content is different, write the new
    // content to the file.
    if !path.exists() || new_content != fs::read(path)? {
        fs::write(path, new_content)?;
    }

    Ok(())
}

fn crate_root(input: &Path) -> io::Result<PathBuf> {
    if input.is_file() {
        return Ok(input.to_owned());
    }
    let roots: Vec<_> = ["src/lib.rs", "src/main.rs", "lib.rs", "main.rs"]
        .iter()
        .map(|name| input.join(name))
        .filter(|path| path.is_file())
        .collect();
    match roots.as_slice() {
        [root] => Ok(root.clone()),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "{} has {} conventional crate roots; pass an explicit Rust file",
                input.display(),
                roots.len()
            ),
        )),
    }
}

pub fn run(opts: CliOptions) -> io::Result<()> {
    let root = crate_root(&opts.path)?;
    let modules = create_translation_to_rocq(&root, opts.axiomatize)?;
    let cwd = std::env::current_dir()?;
    let root_dir = root.canonicalize()?.parent().unwrap().to_owned();
    let mut sources = BTreeMap::new();
    let mut base = if root.is_relative() && root_dir.starts_with(&cwd) {
        cwd
    } else {
        root_dir
    };
    for (filename, (contents, _)) in modules {
        let source = Path::new(&filename).canonicalize().map_err(|err| {
            io::Error::new(
                err.kind(),
                format!("cannot resolve module {filename}: {err}"),
            )
        })?;
        while !source.starts_with(&base) {
            if !base.pop() {
                return Err(io::Error::other(format!(
                    "no common directory for {filename}"
                )));
            }
        }
        if sources.insert(source, contents).is_some() {
            return Err(io::Error::other(format!(
                "duplicate source path for {filename}"
            )));
        }
    }
    sources
        .entry(root.canonicalize()?)
        .or_insert_with(|| crate::header::HEADER.to_owned());
    for (source, contents) in sources {
        let path = opts.output.join(change_to_rocq_extension(
            source.strip_prefix(&base).unwrap(),
        ));
        fs::create_dir_all(path.parent().unwrap())?;
        write_if_changed(&path, contents).map_err(|err| {
            io::Error::new(
                err.kind(),
                format!("cannot write {}: {err}", path.display()),
            )
        })?;
    }
    Ok(())
}

fn create_translation_to_rocq(
    filename: &Path,
    axiomatize: bool,
) -> io::Result<HashMap<String, (String, String)>> {
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .output()?;
    if !out.status.success() {
        return Err(io::Error::other(String::from_utf8_lossy(&out.stderr)));
    }
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();

    println!("Starting to translate {filename:?}...");

    let now = std::time::Instant::now();

    struct TranslateSingleFile {
        axiomatize: bool,
        translation: Option<std::collections::HashMap<String, (String, String)>>,
    }

    impl rustc_driver::Callbacks for TranslateSingleFile {
        fn after_expansion<'tcx>(
            &mut self,
            _compiler: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            self.translation = Some(translate_top_level(
                &tcx,
                TopLevelOptions {
                    axiomatize: self.axiomatize,
                },
            ));
            rustc_driver::Compilation::Stop
        }
    }

    let mut callbacks = TranslateSingleFile {
        axiomatize,
        translation: None,
    };
    let args = vec![
        "rustc".to_string(),
        filename.to_string_lossy().to_string(),
        "--test".to_string(),
        format!("--sysroot={sysroot}"),
    ];

    rustc_driver::run_compiler(&args, &mut callbacks);
    let translation = callbacks
        .translation
        .ok_or_else(|| io::Error::other("rustc returned no translation"))?;

    println!(
        "{} ms have passed to translate: {:?}",
        now.elapsed().as_millis(),
        filename
    );

    Ok(translation)
}
