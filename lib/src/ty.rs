use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::rocq;
use serde::Serialize;
use std::rc::Rc;

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum RocqType {
    Var {
        name: String,
    },
    Path {
        path: Rc<Path>,
    },
    Application {
        func: Rc<RocqType>,
        consts: Vec<Rc<Expr>>,
        tys: Vec<Rc<RocqType>>,
    },
    Function {
        /// We group together the arguments that are called together, as this
        /// will be useful for the monadic translation of types later.
        args: Vec<Rc<RocqType>>,
        ret: Rc<RocqType>,
    },
    Tuple {
        tys: Vec<Rc<RocqType>>,
    },
    // TODO: add the type parameters for the traits
    Dyn {
        traits: Vec<Rc<Path>>,
    },
    AssociatedInTrait {
        trait_name: Rc<Path>,
        const_args: Vec<Rc<Expr>>,
        ty_args: Vec<Rc<RocqType>>,
        self_ty: Rc<RocqType>,
        name: String,
    },
    AssociatedUnknown,
    Infer,
}

impl RocqType {
    pub(crate) fn var(name: &str) -> Rc<RocqType> {
        Rc::new(RocqType::Var {
            name: name.to_string(),
        })
    }

    pub(crate) fn path(segments: &[&str]) -> Rc<RocqType> {
        Rc::new(RocqType::Path {
            path: Path::new(segments),
        })
    }

    pub(crate) fn unit() -> Rc<RocqType> {
        Rc::new(RocqType::Tuple { tys: vec![] })
    }

    pub(crate) fn make_ref(mutbl: &rustc_hir::Mutability, ty: Rc<RocqType>) -> Rc<RocqType> {
        let ptr_name = match mutbl {
            rustc_hir::Mutability::Mut => "&mut",
            rustc_hir::Mutability::Not => "&",
        };

        Rc::new(RocqType::Application {
            func: RocqType::path(&[ptr_name]),
            consts: vec![],
            tys: vec![ty],
        })
    }

    pub(crate) fn match_ref(self: Rc<RocqType>) -> Option<(String, Rc<RocqType>)> {
        if let RocqType::Application { func, consts, tys } = &*self {
            if let RocqType::Path { path, .. } = &**func {
                let Path { segments } = path.as_ref();
                if segments.len() == 1 && consts.is_empty() && tys.len() == 1 {
                    let name = segments.first().unwrap();
                    if name == "&" || name == "&mut" {
                        return Some((name.clone(), tys.first().unwrap().clone()));
                    }
                }
            }
        }

        None
    }
}

pub(crate) fn compile_type<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    ty: &rustc_hir::Ty<'a>,
) -> Rc<RocqType> {
    let generics = env.tcx.generics_of(*local_def_id);
    let item_ctxt = rustc_hir_analysis::collect::ItemCtxt::new(env.tcx, *local_def_id);
    let span = &ty.span;
    let ty = &item_ctxt.lower_ty(ty);

    crate::thir_ty::compile_type(env, span, generics, ty)
}

pub(crate) fn compile_fn_ret_ty<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_ret_ty: &rustc_hir::FnRetTy<'a>,
) -> Rc<RocqType> {
    match fn_ret_ty {
        rustc_hir::FnRetTy::DefaultReturn(_) => RocqType::unit(),
        rustc_hir::FnRetTy::Return(ty) => compile_type(env, local_def_id, ty),
    }
}

// The type of a function declaration
pub(crate) fn compile_fn_decl<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_decl: &rustc_hir::FnDecl<'a>,
) -> Rc<RocqType> {
    let ret = compile_fn_ret_ty(env, local_def_id, &fn_decl.output);

    Rc::new(RocqType::Function {
        args: fn_decl
            .inputs
            .iter()
            .map(|arg| compile_type(env, local_def_id, arg))
            .collect(),
        ret,
    })
}

/// Return the type parameters on a path
pub(crate) fn compile_path_ty_params<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    path: &rustc_hir::Path<'a>,
) -> Vec<Rc<RocqType>> {
    match path.segments.last().unwrap().args {
        Some(args) => args
            .args
            .iter()
            .filter_map(|arg| match arg {
                rustc_hir::GenericArg::Type(ty) => Some(compile_type(env, local_def_id, ty)),
                _ => None,
            })
            .collect(),
        None => vec![],
    }
}

impl RocqType {
    pub(crate) fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            RocqType::Var { name } => rocq::Expression::just_name(name),
            RocqType::Path { path } => rocq::Expression::just_name("Ty.path")
                .apply(Rc::new(rocq::Expression::String(path.to_string()))),
            RocqType::Application { func, consts, tys } => {
                if consts.is_empty() && tys.is_empty() {
                    func.to_rocq()
                } else {
                    rocq::Expression::just_name("Ty.apply").apply_many(&[
                        func.to_rocq(),
                        Rc::new(rocq::Expression::List {
                            exprs: consts.iter().map(|const_| const_.to_rocq()).collect(),
                        }),
                        Rc::new(rocq::Expression::List {
                            exprs: tys.iter().map(|ty| ty.to_rocq()).collect(),
                        }),
                    ])
                }
            }
            RocqType::Function { args, ret } => rocq::Expression::just_name("Ty.function")
                .apply_many(&[
                    Rc::new(rocq::Expression::List {
                        exprs: args.iter().map(|arg| arg.to_rocq()).collect(),
                    }),
                    ret.to_rocq(),
                ]),
            RocqType::Tuple { tys } => {
                rocq::Expression::just_name("Ty.tuple").apply(Rc::new(rocq::Expression::List {
                    exprs: tys.iter().map(|ty| ty.to_rocq()).collect(),
                }))
            }
            RocqType::Dyn { traits } => {
                rocq::Expression::just_name("Ty.dyn").apply(Rc::new(rocq::Expression::List {
                    exprs: traits
                        .iter()
                        .map(|trait_name| {
                            Rc::new(rocq::Expression::Tuple(vec![
                                Rc::new(rocq::Expression::String(trait_name.to_string())),
                                Rc::new(rocq::Expression::List { exprs: vec![] }),
                            ]))
                        })
                        .collect(),
                }))
            }
            RocqType::AssociatedInTrait {
                trait_name,
                const_args,
                ty_args,
                self_ty,
                name,
            } => rocq::Expression::just_name("Ty.associated_in_trait").apply_many(&[
                Rc::new(rocq::Expression::String(trait_name.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: const_args.iter().map(|const_| const_.to_rocq()).collect(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: ty_args.iter().map(|ty| ty.to_rocq()).collect(),
                }),
                self_ty.to_rocq(),
                Rc::new(rocq::Expression::String(name.clone())),
            ]),
            RocqType::AssociatedUnknown => rocq::Expression::just_name("Ty.associated_unknown"),
            RocqType::Infer => Rc::new(rocq::Expression::Wild),
        }
    }

    /// We use this function to get a name for a type for the `impl` sections. This function should
    /// be injective, so that there is no confusion on the `Self` type that might be merged when we
    /// merge multiple modules with the same name.
    pub(crate) fn to_name(&self) -> String {
        match self {
            RocqType::Var { name } => name.clone(),
            RocqType::Path { path, .. } => {
                path.to_name().replace('&', "ref_").replace('*', "pointer_")
            }
            RocqType::Application { func, consts, tys } => {
                let mut name = func.to_name();
                for const_ in consts {
                    name.push('_');
                    name.push_str(&const_.to_name());
                }
                for ty in tys {
                    name.push('_');
                    name.push_str(&ty.to_name());
                }
                name
            }
            RocqType::Function { args, ret } => {
                let mut name = "".to_string();
                for arg in args {
                    name.push_str(&arg.to_name());
                }
                name.push_str("To");
                name.push_str(&ret.to_name());
                name
            }
            RocqType::Tuple { tys } => {
                let mut name = "Tuple_".to_string();
                for ty in tys {
                    name.push_str(&ty.to_name());
                    name.push('_')
                }
                name
            }
            RocqType::Dyn { traits } => {
                let mut name = "Dyn".to_string();
                for trait_ in traits {
                    name.push('_');
                    name.push_str(&trait_.to_name());
                }
                name
            }
            RocqType::AssociatedInTrait {
                trait_name,
                const_args,
                ty_args,
                self_ty,
                name,
            } => {
                format!(
                    "associated_in_trait_{}_{}_{}_{}_{}",
                    trait_name.to_name(),
                    const_args
                        .iter()
                        .map(|const_| const_.to_name())
                        .collect::<Vec<_>>()
                        .join("_"),
                    ty_args
                        .iter()
                        .map(|ty| ty.to_name())
                        .collect::<Vec<_>>()
                        .join("_"),
                    self_ty.to_name(),
                    name
                )
            }
            RocqType::AssociatedUnknown => "associated_unknown_type".to_string(),
            RocqType::Infer => "inferred_type".to_string(),
        }
    }
}
