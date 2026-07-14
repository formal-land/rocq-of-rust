use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use rustc_middle::thir::{Pat, PatKind};
use rustc_type_ir::TyKind;
use std::rc::Rc;

fn compile_literal<'a>(
    ty: rustc_middle::ty::Ty<'a>,
    valtree: rustc_middle::ty::ValTree<'a>,
) -> Option<Rc<Literal>> {
    match &ty.kind() {
        rustc_middle::ty::TyKind::Int(int_ty) => {
            let uint_value = valtree.try_to_scalar_int().unwrap();
            let int_value = uint_value.to_int(uint_value.size());

            Some(Rc::new(Literal::Integer(LiteralInteger {
                kind: capitalize(&format!("{int_ty:?}")),
                negative_sign: int_value < 0,
                // This also handles the absolute value of the minimal i128.
                value: int_value.unsigned_abs(),
            })))
        }
        rustc_middle::ty::TyKind::Uint(uint_ty) => {
            let uint_value = valtree.try_to_scalar_int().unwrap();

            Some(Rc::new(Literal::Integer(LiteralInteger {
                kind: capitalize(&format!("{uint_ty:?}")),
                negative_sign: false,
                value: uint_value.to_bits(uint_value.size()),
            })))
        }
        rustc_middle::ty::TyKind::Char => {
            let char_value = char::from_u32(valtree.try_to_scalar_int().unwrap().to_u32()).unwrap();

            Some(Rc::new(Literal::Char(char_value)))
        }
        _ => None,
    }
}

pub(crate) fn compile_pattern<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    pat: &Pat<'a>,
) -> Rc<Pattern> {
    match &pat.kind {
        PatKind::Wild => Rc::new(Pattern::Wild),
        PatKind::Missing => Rc::new(Pattern::Wild),
        PatKind::AscribeUserType { subpattern, .. } => compile_pattern(env, generics, subpattern),
        PatKind::Binding {
            name,
            mode,
            var: _,
            ty,
            subpattern,
            is_primary: _,
            ..
        } => {
            let name = to_valid_rocq_name(IsValue::Yes, name.as_str());
            let ty = crate::thir_ty::compile_type(env, &pat.span, generics, ty);
            let rustc_ast::ast::BindingMode(by_ref, mutability) = mode;
            let is_with_ref = matches!(by_ref, rustc_ast::ast::ByRef::Yes(..));
            let is_with_mutability = matches!(mutability, rustc_ast::ast::Mutability::Mut);
            let pattern = subpattern
                .as_ref()
                .map(|subpattern| compile_pattern(env, generics, subpattern));
            Rc::new(Pattern::Binding {
                name,
                ty,
                is_with_ref,
                is_with_mutability,
                pattern,
            })
        }
        PatKind::Variant {
            adt_def,
            variant_index,
            subpatterns,
            ..
        } => {
            let variant = adt_def.variant(*variant_index);
            let path = Path::concat(&[
                compile_def_id(env, adt_def.did()),
                Path::new(&[variant.name.as_str()]),
            ]);
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|field| {
                    (
                        variant.fields.get(field.field).unwrap().name.to_string(),
                        compile_pattern(env, generics, &field.pattern),
                    )
                })
                .collect();
            let is_a_tuple = fields
                .iter()
                .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Rc::new(Pattern::StructTuple(path, fields))
            } else {
                Rc::new(Pattern::StructRecord(path, fields))
            }
        }
        PatKind::Leaf { subpatterns } => {
            if let TyKind::Tuple(tys) = &pat.ty.kind() {
                // With the notation `..` some of the fields might be omitted. This is why we
                // first create a fields of wildcards and then replace the ones that are
                // present in the pattern.
                let mut fields: Vec<_> = tys.iter().map(|_| Rc::new(Pattern::Wild)).collect();

                for subpattern in subpatterns {
                    fields[subpattern.field.index()] =
                        compile_pattern(env, generics, &subpattern.pattern);
                }

                return Rc::new(Pattern::Tuple(fields));
            }
            let adt_def = pat.ty.ty_adt_def().unwrap();
            let path = compile_def_id(env, adt_def.did());
            let variant = adt_def.non_enum_variant();
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|field| {
                    (
                        variant.fields.get(field.field).unwrap().name.to_string(),
                        compile_pattern(env, generics, &field.pattern),
                    )
                })
                .collect();
            let is_a_tuple = fields
                .iter()
                .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Rc::new(Pattern::StructTuple(path, fields))
            } else {
                Rc::new(Pattern::StructRecord(path, fields))
            }
        }
        PatKind::Deref { subpattern } => {
            Rc::new(Pattern::Deref(compile_pattern(env, generics, subpattern)))
        }
        PatKind::Constant { value } => {
            {
                let ty = value.ty;
                // Brutal way to handle the case of rustc_middle::ty::TyKind::Str
                // Since the type would be erased when it comes down to THIR level
                // TODO: have a translation that works for all strings
                let kind_name = format!("{:?}", ty.kind());
                if kind_name == "&'{erased} str" {
                    let string_value = value.to_string();
                    // The generated string comes with extra "" so we trim the 1st and last character out
                    let mut chars = string_value.chars();
                    chars.next();
                    chars.next_back();
                    let string_value = chars.as_str();
                    return Rc::new(Pattern::Literal(Rc::new(Literal::String(
                        string_value.to_string(),
                    ))));
                }
                // And for the rest...
                if let rustc_middle::ty::TyKind::Bool = ty.kind() {
                    return Rc::new(Pattern::Literal(Rc::new(Literal::Bool(
                        value.try_to_bool().unwrap(),
                    ))));
                }
                if let Some(literal) = compile_literal(ty, value.valtree) {
                    return Rc::new(Pattern::Literal(literal));
                }
            }
            emit_warning_with_note(
                env,
                &pat.span,
                "This kind of constant in patterns is not yet supported.",
                None,
            );

            Rc::new(Pattern::Wild)
        }
        PatKind::Range(range) => {
            if !matches!(
                range.ty.kind(),
                rustc_middle::ty::TyKind::Int(_) | rustc_middle::ty::TyKind::Uint(_)
            ) {
                emit_warning_with_note(
                    env,
                    &pat.span,
                    "Only integer ranges in patterns are currently supported.",
                    None,
                );

                return Rc::new(Pattern::Wild);
            }
            let lower_bound = match range.lo {
                rustc_middle::thir::PatRangeBoundary::NegInfinity => None,
                rustc_middle::thir::PatRangeBoundary::Finite(value) => {
                    let Some(literal) = compile_literal(range.ty, value) else {
                        emit_warning_with_note(
                            env,
                            &pat.span,
                            "This kind of lower range bound is not yet supported.",
                            None,
                        );

                        return Rc::new(Pattern::Wild);
                    };

                    Some(literal)
                }
                rustc_middle::thir::PatRangeBoundary::PosInfinity => {
                    emit_warning_with_note(
                        env,
                        &pat.span,
                        "Unexpected positive infinity as a lower range bound.",
                        None,
                    );

                    return Rc::new(Pattern::Wild);
                }
            };
            let upper_bound = match range.hi {
                rustc_middle::thir::PatRangeBoundary::PosInfinity => None,
                rustc_middle::thir::PatRangeBoundary::Finite(value) => {
                    let Some(literal) = compile_literal(range.ty, value) else {
                        emit_warning_with_note(
                            env,
                            &pat.span,
                            "This kind of upper range bound is not yet supported.",
                            None,
                        );

                        return Rc::new(Pattern::Wild);
                    };

                    Some(literal)
                }
                rustc_middle::thir::PatRangeBoundary::NegInfinity => {
                    emit_warning_with_note(
                        env,
                        &pat.span,
                        "Unexpected negative infinity as an upper range bound.",
                        None,
                    );

                    return Rc::new(Pattern::Wild);
                }
            };

            Rc::new(Pattern::Range {
                lower_bound,
                upper_bound,
                is_inclusive: range.end == rustc_hir::RangeEnd::Included,
            })
        }
        PatKind::Slice {
            prefix,
            slice,
            suffix,
        }
        | PatKind::Array {
            prefix,
            slice,
            suffix,
        } => {
            let prefix: Vec<Rc<Pattern>> = prefix
                .iter()
                .map(|pat| compile_pattern(env, generics, pat))
                .collect();
            let suffix: Vec<Rc<Pattern>> = suffix
                .iter()
                .map(|pat| compile_pattern(env, generics, pat))
                .collect();
            let slice_pattern: Option<Rc<Pattern>> = slice
                .as_ref()
                .map(|pat_middle| compile_pattern(env, generics, pat_middle));
            Rc::new(Pattern::Slice {
                prefix_patterns: prefix,
                slice_pattern,
                suffix_patterns: suffix,
            })
        }
        PatKind::Or { pats } => Rc::new(Pattern::Or(
            pats.iter()
                .map(|pat| compile_pattern(env, generics, pat))
                .collect(),
        )),
        PatKind::Never => {
            emit_warning_with_note(
                env,
                &pat.span,
                "Never patterns are not yet supported.",
                None,
            );

            Rc::new(Pattern::Wild)
        }
        PatKind::Error(_) => {
            emit_warning_with_note(
                env,
                &pat.span,
                "Error patterns are not yet supported.",
                None,
            );

            Rc::new(Pattern::Wild)
        }
        PatKind::DerefPattern { .. } => {
            emit_warning_with_note(
                env,
                &pat.span,
                "Deref patterns are not yet supported.",
                None,
            );

            Rc::new(Pattern::Wild)
        }
        PatKind::ExpandedConstant { subpattern, .. } => compile_pattern(env, generics, subpattern),
    }
}
