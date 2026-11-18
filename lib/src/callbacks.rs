use crate::options::Options;
use crate::top_level::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use std::collections::BTreeMap;
use std::path::Path;

pub struct ToRocq {
    opts: Options,
}

impl ToRocq {
    pub fn new(opts: Options) -> Self {
        ToRocq { opts }
    }
}

fn write_output(compiler: &Compiler, path: &Path, contents: &str) {
    if let Err(err) = crate::core::write_if_changed(path, contents) {
        compiler
            .sess
            .dcx()
            .fatal(format!("cannot write {}: {err}", path.display()));
    }
    // Cargo must re-run the wrapper if a generated artifact disappears.
    compiler
        .sess
        .psess
        .file_depinfo
        .borrow_mut()
        .insert(Symbol::intern(&path.to_string_lossy()));
}

impl Callbacks for ToRocq {
    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let crate::options::Options {
            axiomatize,
            with_json,
            ..
        } = self.opts;

        let current_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
        let current_crate_name_string = current_crate_name.to_string();

        println!("Compiling crate {current_crate_name_string:}");

        let crate_name = current_crate_name_string.clone();
        let translation = translate_top_level(&tcx, TopLevelOptions { axiomatize });

        let mut index = String::new();
        for (file_name, (rocq, json)) in BTreeMap::from_iter(translation) {
            let source = Path::new(&file_name);
            // Expansion spans in the virtual sysroot are not crate-owned modules.
            if source.starts_with("/rustc") && !source.exists() {
                continue;
            }
            write_output(compiler, &source.with_extension("v"), &rocq);
            if with_json {
                write_output(compiler, &source.with_extension("json"), &json);
            }
            let module = source
                .with_extension("")
                .to_string_lossy()
                .replace('/', ".");
            index.push_str(&format!("Require Export {module}.\n"));
        }
        write_output(compiler, Path::new(&format!("{crate_name}.v")), &index);

        if self.opts.in_cargo {
            let key = "ROCQ_OF_RUST_ARGS";
            compiler.sess.psess.env_depinfo.borrow_mut().insert((
                Symbol::intern(key),
                std::env::var(key).ok().map(|args| Symbol::intern(&args)),
            ));
            let driver = std::env::current_exe().expect("current driver path");
            compiler
                .sess
                .psess
                .file_depinfo
                .borrow_mut()
                .insert(Symbol::intern(&driver.to_string_lossy()));
        }

        compiler.sess.dcx().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
