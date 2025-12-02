use crate::env::*;
use crate::path::*;
use crate::thir_expression::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_span::def_id::DefId;
use rustc_type_ir::TyKind;
use std::rc::Rc;

pub(crate) fn compile_generic_param(env: &Env, def_id: DefId) -> String {
    to_valid_rocq_name(
        IsValue::No,
        compile_def_id(env, def_id).segments.last().unwrap(),
    )
}

fn compile_poly_fn_sig<'a>(
    env: &Env<'a>,
    span: &rustc_span::Span,
    generics: &'a rustc_middle::ty::Generics,
    sig: &rustc_middle::ty::PolyFnSig<'a>,
    from_closure: bool,
) -> Rc<RocqType> {
    let sig = sig.skip_binder();
    let args = sig
        .inputs()
        .iter()
        .map(|ty| compile_type(env, span, generics, ty))
        .collect::<Vec<_>>();
    let args = if from_closure {
        if let Some(arg) = args.first() {
            if let RocqType::Tuple { tys } = arg.as_ref() {
                tys.to_vec()
            } else {
                panic!("Expected a tuple for the first argument of a closure");
            }
        } else {
            panic!("Expected a tuple for the first argument of a closure");
        }
    } else {
        args
    };
    let ret = compile_type(env, span, generics, &sig.output());

    Rc::new(RocqType::Function { args, ret })
}

/// The [generics] parameter is the list of generic types available in the
/// current environment. It is required to disambiguate the names of the
/// occurrences of these generic types. It is possible to have twice the same
/// name for a generic type, especially with `impl Trait` types that are
/// represented as generics of the name "impl Trait".
pub(crate) fn compile_type<'a>(
    env: &Env<'a>,
    span: &rustc_span::Span,
    generics: &'a rustc_middle::ty::Generics,
    ty: &rustc_middle::ty::Ty<'a>,
) -> Rc<RocqType> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            RocqType::path(&[&ty.to_string()])
        }
        TyKind::Adt(adt_def, substs) => {
            let path = compile_def_id(env, adt_def.did());
            let consts = substs
                .iter()
                .filter_map(|subst| match &subst.unpack() {
                    GenericArgKind::Const(constant) => Some(compile_const(env, span, constant)),
                    _ => None,
                })
                .collect();
            let tys = substs
                .iter()
                .filter_map(|subst| match &subst.unpack() {
                    GenericArgKind::Type(ty) => Some(compile_type(env, span, generics, ty)),
                    _ => None,
                })
                .collect();
            Rc::new(RocqType::Application {
                func: Rc::new(RocqType::Path { path }),
                consts,
                tys,
            })
        }
        TyKind::Foreign(def_id) => Rc::new(RocqType::Path {
            path: compile_def_id(env, *def_id),
        }),
        TyKind::Str => RocqType::path(&["str"]),
        TyKind::Array(ty, const_) => Rc::new(RocqType::Application {
            func: RocqType::path(&["array"]),
            consts: vec![compile_const(env, span, const_)],
            tys: vec![compile_type(env, span, generics, ty)],
        }),
        TyKind::Slice(ty) => Rc::new(RocqType::Application {
            func: RocqType::path(&["slice"]),
            consts: vec![],
            tys: vec![compile_type(env, span, generics, ty)],
        }),
        TyKind::RawPtr(ty, mutability) => {
            let ptr_name = match mutability {
                rustc_hir::Mutability::Mut => "*mut",
                rustc_hir::Mutability::Not => "*const",
            };

            Rc::new(RocqType::Application {
                func: RocqType::path(&[ptr_name]),
                consts: vec![],
                tys: vec![compile_type(env, span, generics, ty)],
            })
        }
        TyKind::Ref(_, ty, mutbl) => {
            RocqType::make_ref(mutbl, compile_type(env, span, generics, ty))
        }
        TyKind::FnPtr(fn_sig, fn_header) => {
            compile_poly_fn_sig(env, span, generics, &fn_sig.with(*fn_header), false)
        }
        TyKind::Dynamic(existential_predicates, _, _) => {
            let traits = existential_predicates
                .iter()
                .filter_map(
                    |existential_predicate| match existential_predicate.no_bound_vars() {
                        None => Some(Path::new(&["existential predicate with variables"])),
                        Some(existential_predicate) => match existential_predicate {
                            rustc_middle::ty::ExistentialPredicate::Trait(
                                existential_trait_ref,
                            ) => Some(Path::concat(&[
                                compile_def_id(env, existential_trait_ref.def_id),
                                Path::new(&["Trait"]),
                            ])),
                            rustc_middle::ty::ExistentialPredicate::AutoTrait(def_id) => {
                                Some(Path::concat(&[
                                    compile_def_id(env, def_id),
                                    Path::new(&["AutoTrait"]),
                                ]))
                            }
                            _ => None,
                        },
                    },
                )
                .collect();

            Rc::new(RocqType::Dyn { traits })
        }
        TyKind::FnDef(_, _) => {
            let fn_sig = ty.fn_sig(env.tcx);

            compile_poly_fn_sig(env, span, generics, &fn_sig, false)
        }
        TyKind::Closure(_, generic_args) => {
            let fn_sig = generic_args.as_closure().sig();

            compile_poly_fn_sig(env, span, generics, &fn_sig, true)
        }
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => RocqType::path(&["never"]),
        TyKind::Tuple(tys) => Rc::new(RocqType::Tuple {
            tys: tys
                .iter()
                .map(|ty| compile_type(env, span, generics, &ty))
                .collect(),
        }),
        TyKind::Alias(alias_kind, alias_ty) => match alias_kind {
            rustc_middle::ty::AliasTyKind::Projection => {
                let self_ty = compile_type(env, span, generics, &alias_ty.self_ty());
                let (trait_ref, _own_args) = alias_ty.trait_ref_and_own_args(env.tcx);
                let trait_name = compile_def_id(env, trait_ref.def_id);
                let const_args = alias_ty
                    .args
                    .iter()
                    // We skip the first argument because it is the Self type
                    .skip(1)
                    .filter_map(|generic_arg| {
                        generic_arg
                            .as_const()
                            .as_ref()
                            .map(|constant| compile_const(env, span, constant))
                    })
                    .collect();
                let ty_args = alias_ty
                    .args
                    .iter()
                    // We skip the first argument because it is the Self type
                    .skip(1)
                    .filter_map(|generic_arg| {
                        generic_arg
                            .as_type()
                            .as_ref()
                            .map(|ty| compile_type(env, span, generics, ty))
                    })
                    .collect();
                let path = compile_def_id(env, alias_ty.def_id);

                Rc::new(RocqType::AssociatedInTrait {
                    trait_name,
                    const_args,
                    ty_args,
                    self_ty,
                    name: path.segments.last().unwrap().clone(),
                })
            }
            _ => Rc::new(RocqType::AssociatedUnknown),
        },
        TyKind::Param(param) => {
            if generics.has_self && param.index == 0 {
                return RocqType::var("Self");
            }

            let type_param = generics.type_param(*param, env.tcx);

            RocqType::var(compile_generic_param(env, type_param.def_id).as_ref())
        }
        // Bound(DebruijnIndex, BoundTy),
        // Placeholder(Placeholder<BoundTy>),
        TyKind::Infer(_) => Rc::new(RocqType::Infer),
        TyKind::Error(error) => RocqType::var(&format!("error: {error:#?}")),
        _ => RocqType::var(&format!("type {:#?} not yet handled", ty.kind())),
    }
}
