//! Check the dual-mode source convention before translating the staged input.
//! Conditional executable statements can give Verus and the Rust translator
//! different function bodies even when the file hash agrees.
use std::path::Path;
use syn::punctuated::Punctuated;
use syn::visit::{self, Visit};
use syn::{Attribute, ItemUse, Macro, Meta, StmtMacro, Token};

fn verus_only(attr: &Attribute) -> bool {
    attr.path().is_ident("cfg")
        && attr
            .parse_args::<syn::Ident>()
            .is_ok_and(|id| id == "verus_only")
}

#[derive(Default)]
struct SharedBody {
    errors: Vec<&'static str>,
}

impl<'ast> Visit<'ast> for SharedBody {
    fn visit_item_use(&mut self, item: &'ast ItemUse) {
        let vstd = matches!(&item.tree, syn::UseTree::Path(path) if path.ident == "vstd");
        if vstd && item.attrs.len() == 1 && verus_only(&item.attrs[0]) {
            return;
        }
        visit::visit_item_use(self, item);
    }

    fn visit_stmt_macro(&mut self, stmt: &'ast StmtMacro) {
        if stmt.mac.path.is_ident("proof") && stmt.attrs.len() == 1 && verus_only(&stmt.attrs[0]) {
            return;
        }
        visit::visit_stmt_macro(self, stmt);
    }

    fn visit_macro(&mut self, _: &'ast Macro) {
        self.errors
            .push("executable macro expansion is outside the shared-body fragment");
    }

    fn visit_attribute(&mut self, attr: &'ast Attribute) {
        if attr.path().is_ident("cfg_attr") {
            let args = attr.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated);
            if let Ok(args) = args {
                if args.len() == 2 && args[0].path().is_ident("verus_only") {
                    let spec = &args[1];
                    if spec.path().is_ident("verus_spec") || spec.path().is_ident("verus_verify") {
                        return;
                    }
                    if let Meta::List(feature) = spec {
                        if feature.path.is_ident("feature")
                            && feature
                                .parse_args::<syn::Ident>()
                                .is_ok_and(|id| id == "proc_macro_hygiene")
                        {
                            return;
                        }
                    }
                }
            }
            self.errors
                .push("unsupported conditional attribute on shared Rust code");
        } else if attr.path().is_ident("cfg") {
            self.errors
                .push("conditional executable Rust can change the verified function body");
        } else if ![
            "doc", "allow", "warn", "deny", "forbid", "inline", "repr", "derive",
        ]
        .iter()
        .any(|name| attr.path().is_ident(name))
        {
            self.errors
                .push("unsupported attribute on shared Rust code");
        }
    }
}

pub fn check(path: &Path) -> Result<(), String> {
    let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let ast = syn::parse_file(&source).map_err(|e| e.to_string())?;
    let mut check = SharedBody::default();
    check.visit_file(&ast);
    check
        .errors
        .first()
        .map_or(Ok(()), |error| Err(error.to_string()))
}
