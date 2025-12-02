use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::rocq;
use crate::ty::*;
use core::panic;
use itertools::Itertools;
use rustc_middle::query::plumbing::IntoQueryParam;
use serde::Serialize;
use std::rc::Rc;

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug, Serialize)]
pub(crate) struct MatchArm {
    pub(crate) pattern: Rc<Pattern>,
    /// We represent a boolean guard as an if-let guard with a pattern
    /// equals to the boolean [true]. Thus we do not need to distinguish
    /// between boolean guards and if-let guards in the translation. There can
    /// be a list of conditions, for guards having several conditions separated
    /// by the `&&` operator.
    pub(crate) if_let_guard: Vec<(Rc<Pattern>, Rc<Expr>)>,
    pub(crate) body: Rc<Expr>,
}

/// [LoopControlFlow] represents the expressions responsible for
/// the flow of control in a loop
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub(crate) enum LoopControlFlow {
    Continue,
    Break,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub(crate) enum CallKind {
    /// Pure call of a function, written with a space following the syntax
    /// of Rocq.
    Pure,
    /// Like [Pure] but with a result in the monad.
    Effectful,
    /// Call of a Rust closure, using the monadic operator `M.call`. We give the return type.
    Closure(Rc<RocqType>),
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) struct LiteralInteger {
    pub(crate) kind: String,
    pub(crate) negative_sign: bool,
    pub(crate) value: u128,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum Literal {
    Bool(bool),
    Integer(LiteralInteger),
    Char(char),
    String(String),
    Error,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum LambdaForm {
    Closure,
    Function,
    ListFunction,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum PointerCoercionSafety {
    Unsafe,
    Safe,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum PointerCoercion {
    ReifyFnPointer,
    UnsafeFnPointer,
    ClosureFnPointer(PointerCoercionSafety),
    MutToConstPointer,
    ArrayToPointer,
    Unsize,
    DynStar,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum Expr {
    LocalVar(String),
    GetConstant {
        path: Rc<Path>,
        return_ty: Rc<RocqType>,
    },
    GetAssociatedConstant {
        ty: Rc<RocqType>,
        constant: String,
        return_ty: Rc<RocqType>,
    },
    GetFunction {
        func: Rc<Path>,
        generic_consts: Vec<Rc<Expr>>,
        generic_tys: Vec<Rc<RocqType>>,
    },
    GetTraitMethod {
        trait_name: Rc<Path>,
        self_ty: Rc<RocqType>,
        trait_consts: Vec<Rc<Expr>>,
        trait_tys: Vec<Rc<RocqType>>,
        method_name: String,
        generic_consts: Vec<Rc<Expr>>,
        generic_tys: Vec<Rc<RocqType>>,
    },
    GetAssociatedFunction {
        ty: Rc<RocqType>,
        func: String,
        generic_consts: Vec<Rc<Expr>>,
        generic_tys: Vec<Rc<RocqType>>,
    },
    Literal(Rc<Literal>),
    ConstructorAsClosure {
        path: Rc<Path>,
        generic_consts: Vec<Rc<Expr>>,
        generic_tys: Vec<Rc<RocqType>>,
    },
    Call {
        func: Rc<Expr>,
        args: Vec<Rc<Expr>>,
        kind: CallKind,
    },
    CallTy {
        func: Rc<Expr>,
        ty: Rc<RocqType>,
    },
    Alloc {
        ty: Rc<RocqType>,
        expr: Rc<Expr>,
    },
    /// The logical operators are lazily evaluated, so the second
    /// parameter [rhs] must be in monadic form.
    LogicalOperator {
        name: String,
        lhs: Rc<Expr>,
        rhs: Rc<Expr>,
    },
    Cast {
        target_ty: Rc<RocqType>,
        source: Rc<Expr>,
    },
    Lambda {
        args: Vec<(String, Option<Rc<RocqType>>)>,
        body: Rc<Expr>,
        is_for_match: bool,
        form: LambdaForm,
    },
    Array {
        elements: Vec<Rc<Expr>>,
        is_internal: bool,
    },
    Tuple {
        elements: Vec<Rc<Expr>>,
    },
    Let {
        name: Option<String>,
        ty: Option<Rc<RocqType>>,
        init: Rc<Expr>,
        body: Rc<Expr>,
    },
    Match {
        ty: Rc<RocqType>,
        scrutinee: Rc<Expr>,
        arms: Vec<Rc<Expr>>,
    },
    PointerCoercion {
        coercion: PointerCoercion,
        source_ty: Rc<RocqType>,
        target_ty: Rc<RocqType>,
    },
    Loop {
        ty: Rc<RocqType>,
        body: Rc<Expr>,
    },
    Index {
        base: Rc<Expr>,
        index: Rc<Expr>,
    },
    ControlFlow(LoopControlFlow),
    StructStruct {
        path: Rc<Path>,
        arg_consts: Vec<Rc<Expr>>,
        arg_tys: Vec<Rc<RocqType>>,
        fields: Vec<(String, Rc<Expr>)>,
        base: Option<Rc<Expr>>,
    },
    StructTuple {
        path: Rc<Path>,
        arg_consts: Vec<Rc<Expr>>,
        arg_tys: Vec<Rc<RocqType>>,
        fields: Vec<Rc<Expr>>,
    },
    Use(Rc<Expr>),
    InternalString(String),
    InternalInteger(usize),
    Return(Rc<Expr>),
    /// Useful for error messages or annotations
    Comment(String, Rc<Expr>),
    Ty(Rc<RocqType>),
}

impl Expr {
    pub(crate) fn tt() -> Rc<Self> {
        Rc::new(Expr::Tuple { elements: vec![] }).alloc(RocqType::unit())
    }

    pub(crate) fn local_var(name: &str) -> Rc<Expr> {
        Rc::new(Expr::LocalVar(name.to_string()))
    }

    pub(crate) fn alloc(self: Rc<Self>, ty: Rc<RocqType>) -> Rc<Self> {
        Rc::new(Expr::Alloc { ty, expr: self })
    }

    pub(crate) fn read(self: &Rc<Self>) -> Rc<Self> {
        // If we read an allocated expression, we just return the expression.
        if let Expr::Alloc { ty: _, expr } = self.as_ref() {
            return expr.clone();
        }

        Rc::new(Expr::Call {
            func: Expr::local_var("M.read"),
            args: vec![self.clone()],
            kind: CallKind::Effectful,
        })
    }

    pub(crate) fn copy(self: Rc<Self>, ty: Rc<RocqType>) -> Rc<Self> {
        if let Expr::Alloc { .. } = self.as_ref() {
            return self;
        }

        Rc::new(Expr::Call {
            func: Expr::local_var("M.copy"),
            args: vec![Rc::new(Expr::Ty(ty)), self],
            kind: CallKind::Effectful,
        })
    }

    /// If the body of the function is the macro call `unimplemented!()`. We do
    /// a special treatment for this case, by translating the function directly
    /// to an axiom. That is useful for mocks, where we want to state them equal
    /// to something defined in Rocq at proof time. This is not wrong in the
    /// translation as we are only losing information here, not stating
    /// something wrong.
    pub(crate) fn is_unimplemented(self: &Rc<Self>) -> bool {
        *self.as_ref()
            == Expr::Call {
                func: Expr::local_var("M.never_to_any"),
                kind: CallKind::Effectful,
                args: vec![Rc::new(Expr::Call {
                    func: Rc::new(Expr::GetFunction {
                        func: Path::new(&["core", "panicking", "panic"]),
                        generic_consts: vec![],
                        generic_tys: vec![],
                    }),
                    kind: CallKind::Closure(RocqType::path(&["never"])),
                    args: vec![Rc::new(Expr::Call {
                        func: Expr::local_var("M.read"),
                        kind: CallKind::Effectful,
                        args: vec![Rc::new(Expr::Literal(Rc::new(Literal::String(
                            "not implemented".to_string(),
                        ))))],
                    })],
                })],
            }
    }

    pub(crate) fn has_return(&self) -> bool {
        match self {
            Expr::LocalVar(_) => false,
            Expr::GetConstant { .. } => false,
            Expr::GetAssociatedConstant { .. } => false,
            Expr::GetFunction { .. } => false,
            Expr::GetTraitMethod { .. } => false,
            Expr::GetAssociatedFunction { .. } => false,
            Expr::Literal(_) => false,
            Expr::ConstructorAsClosure { .. } => false,
            Expr::Call {
                func,
                args,
                kind: _,
            } => func.has_return() || args.iter().any(|arg| arg.has_return()),
            Expr::CallTy { func, ty: _ } => func.has_return(),
            Expr::Alloc { ty: _, expr } => expr.has_return(),
            Expr::LogicalOperator { name: _, lhs, rhs } => lhs.has_return() || rhs.has_return(),
            Expr::Cast {
                target_ty: _,
                source,
            } => source.has_return(),
            Expr::Lambda {
                args: _,
                body,
                is_for_match,
                form: _,
            } => *is_for_match && body.has_return(),
            Expr::Array {
                elements,
                is_internal: _,
            } => elements.iter().any(|element| element.has_return()),
            Expr::Tuple { elements } => elements.iter().any(|element| element.has_return()),
            Expr::Let {
                name: _,
                ty: _,
                init,
                body,
            } => init.has_return() || body.has_return(),
            Expr::PointerCoercion {
                coercion: _,
                source_ty: _,
                target_ty: _,
            } => false,
            Expr::Loop { ty: _, body } => body.has_return(),
            Expr::Match {
                ty: _,
                scrutinee,
                arms,
            } => scrutinee.has_return() || arms.iter().any(|arm| arm.has_return()),
            Expr::Index { base, index } => base.has_return() || index.has_return(),
            Expr::ControlFlow(_) => false,
            Expr::StructStruct {
                path: _,
                arg_consts: _,
                arg_tys: _,
                fields,
                base,
            } => {
                fields.iter().any(|(_, field)| field.has_return())
                    || base.iter().any(|base| base.has_return())
            }
            Expr::StructTuple {
                path: _,
                arg_consts: _,
                arg_tys: _,
                fields,
            } => fields.iter().any(|field| field.has_return()),
            Expr::Use(expr) => expr.has_return(),
            Expr::InternalString(_) => false,
            Expr::InternalInteger(_) => false,
            Expr::Return(_) => true,
            Expr::Comment(_, expr) => expr.has_return(),
            Expr::Ty(_) => false,
        }
    }
}

pub(crate) fn apply_on_thir<'a, F, A>(
    env: &Env<'a>,
    local_def_id: impl IntoQueryParam<rustc_span::def_id::LocalDefId>,
    f: F,
) -> Result<A, String>
where
    F: FnOnce(&rustc_middle::thir::Thir<'a>, &rustc_middle::thir::ExprId) -> A,
{
    let thir = env.tcx.thir_body(local_def_id);
    let Ok((thir, expr_id)) = thir else {
        return Result::Err("thir failed to compile".to_string());
    };
    let result = std::panic::catch_unwind(panic::AssertUnwindSafe(|| thir.borrow()));

    match result {
        Ok(thir) => Result::Ok(f(&thir, &expr_id)),
        Err(error) => Result::Err(format!("thir failed to compile: {:?}", error)),
    }
}

pub(crate) fn compile_hir_id(env: &Env, hir_id: rustc_hir::hir_id::HirId) -> Rc<Expr> {
    let local_def_id = hir_id.owner.def_id;
    let result = apply_on_thir(env, local_def_id, |thir, expr_id| {
        let generics = env.tcx.generics_of(local_def_id);

        crate::thir_expression::compile_expr(env, generics, thir, expr_id)
    });

    match result {
        Ok(expr) => expr,
        Err(error) => Rc::new(Expr::Comment(error, Expr::tt())),
    }
}

#[derive(Debug)]
enum StringPiece {
    /// A string of ASCII characters
    AsciiString(String),
    /// A single non-ASCII character
    UnicodeChar(char),
}

/// As we can only represent purely ASCII strings in Rocq, we need to cut the
/// string in pieces, alternating between ASCII strings and non-ASCII
/// characters.
fn cut_string_in_pieces_for_rocq(input: &str) -> Vec<StringPiece> {
    let mut result: Vec<StringPiece> = Vec::new();
    let mut ascii_buf = String::new();

    for c in input.chars() {
        if c.is_ascii() {
            ascii_buf.push(c);
        } else {
            if !ascii_buf.is_empty() {
                result.push(StringPiece::AsciiString(ascii_buf.clone()));
                ascii_buf.clear();
            }
            result.push(StringPiece::UnicodeChar(c));
        }
    }

    if !ascii_buf.is_empty() {
        result.push(StringPiece::AsciiString(ascii_buf));
    }
    result
}

fn string_pieces_to_rocq(pieces: &[StringPiece]) -> Rc<rocq::Expression> {
    match pieces {
        [] => rocq::Expression::just_name("\"\""),
        [StringPiece::AsciiString(s), rest @ ..] => {
            let head = Rc::new(rocq::Expression::String(str::replace(s, "\"", "\"\"")));
            if rest.is_empty() {
                head
            } else {
                rocq::Expression::just_name("PrimString.cat")
                    .apply_many(&[head, string_pieces_to_rocq(rest)])
            }
        }
        [StringPiece::UnicodeChar(c), rest @ ..] => rocq::Expression::just_name("PrimString.cat")
            .apply_many(&[
                rocq::Expression::just_name("PrimString.make").apply_many(&[
                    Rc::new(rocq::Expression::U128(1)),
                    Rc::new(rocq::Expression::InScope(
                        Rc::new(rocq::Expression::U128(*c as u128)),
                        "int63".to_string(),
                    )),
                ]),
                string_pieces_to_rocq(rest),
            ]),
    }
}

fn string_to_rocq(message: &str) -> Rc<rocq::Expression> {
    let pieces = cut_string_in_pieces_for_rocq(message);
    rocq::Expression::just_name("mk_str").monadic_apply(string_pieces_to_rocq(&pieces))
}

impl LoopControlFlow {
    pub fn to_rocq(self) -> Rc<rocq::Expression> {
        match self {
            LoopControlFlow::Break => rocq::Expression::just_name("M.break").monadic_apply_empty(),
            LoopControlFlow::Continue => {
                rocq::Expression::just_name("M.continue").monadic_apply_empty()
            }
        }
    }
}

impl Literal {
    pub(crate) fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            Literal::Bool(b) => rocq::Expression::just_name("Value.Bool")
                .apply(rocq::Expression::just_name(b.to_string().as_str())),
            Literal::Integer(LiteralInteger {
                kind,
                negative_sign,
                value,
            }) => rocq::Expression::just_name("Value.Integer").apply_many(&[
                rocq::Expression::just_name(format!("IntegerKind.{kind}").as_str()),
                if *negative_sign {
                    rocq::Expression::just_name(format!("(-{value})").as_str())
                } else {
                    rocq::Expression::just_name(value.to_string().as_str())
                },
            ]),
            Literal::Char(c) => rocq::Expression::just_name("Value.UnicodeChar").apply(
                rocq::Expression::just_name((*c as u32).to_string().as_str()),
            ),
            Literal::String(s) => string_to_rocq(s.as_str()),
            Literal::Error => rocq::Expression::just_name("UnsupportedLiteral"),
        }
    }

    fn to_name(&self) -> String {
        match self {
            Literal::Bool(b) => b.to_string(),
            Literal::Integer(LiteralInteger {
                kind,
                negative_sign,
                value,
            }) => {
                if *negative_sign {
                    format!("{kind}_minus_{value}")
                } else {
                    format!("{kind}_{value}")
                }
            }
            Literal::Char(c) => format!("char_{}", c),
            Literal::String(s) => format!("string_{}", s),
            Literal::Error => "error".to_string(),
        }
    }
}

impl PointerCoercionSafety {
    pub(crate) fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            PointerCoercionSafety::Unsafe => {
                rocq::Expression::just_name("M.PointerCoercion.Safety.Unsafe")
            }
            PointerCoercionSafety::Safe => {
                rocq::Expression::just_name("M.PointerCoercion.Safety.Safe")
            }
        }
    }
}

impl PointerCoercion {
    pub(crate) fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            PointerCoercion::ReifyFnPointer => {
                rocq::Expression::just_name("M.PointerCoercion.ReifyFnPointer")
            }
            PointerCoercion::UnsafeFnPointer => {
                rocq::Expression::just_name("M.PointerCoercion.UnsafeFnPointer")
            }
            PointerCoercion::ClosureFnPointer(safety) => {
                rocq::Expression::just_name("M.PointerCoercion.ClosureFnPointer")
                    .apply(safety.to_rocq())
            }
            PointerCoercion::MutToConstPointer => {
                rocq::Expression::just_name("M.PointerCoercion.MutToConstPointer")
            }
            PointerCoercion::ArrayToPointer => {
                rocq::Expression::just_name("M.PointerCoercion.ArrayToPointer")
            }
            PointerCoercion::Unsize => rocq::Expression::just_name("M.PointerCoercion.Unsize"),
            PointerCoercion::DynStar => rocq::Expression::just_name("M.PointerCoercion.DynStar"),
        }
    }
}

impl Expr {
    pub(crate) fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            Expr::LocalVar(ref name) => rocq::Expression::just_name(name),
            Expr::GetConstant { path, return_ty } => rocq::Expression::just_name("get_constant")
                .monadic_apply_many(&[
                    Rc::new(rocq::Expression::String(path.to_string())),
                    return_ty.to_rocq(),
                ]),
            Expr::GetAssociatedConstant {
                ty,
                constant,
                return_ty,
            } => rocq::Expression::just_name("get_associated_constant").monadic_apply_many(&[
                ty.to_rocq(),
                Rc::new(rocq::Expression::String(constant.to_string())),
                return_ty.to_rocq(),
            ]),
            Expr::GetFunction {
                func,
                generic_consts,
                generic_tys,
            } => rocq::Expression::just_name("M.get_function").monadic_apply_many(&[
                Rc::new(rocq::Expression::String(func.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: generic_consts
                        .iter()
                        .map(|generic_const| generic_const.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: generic_tys
                        .iter()
                        .map(|generic_ty| generic_ty.to_rocq())
                        .collect_vec(),
                }),
            ]),
            Expr::GetTraitMethod {
                trait_name,
                self_ty,
                trait_consts,
                trait_tys,
                method_name,
                generic_consts,
                generic_tys,
            } => rocq::Expression::just_name("M.get_trait_method").monadic_apply_many(&[
                Rc::new(rocq::Expression::String(trait_name.to_string())),
                self_ty.to_rocq(),
                Rc::new(rocq::Expression::List {
                    exprs: trait_consts
                        .iter()
                        .map(|trait_const| trait_const.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: trait_tys
                        .iter()
                        .map(|trait_ty| trait_ty.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::String(method_name.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: generic_consts
                        .iter()
                        .map(|const_| const_.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: generic_tys.iter().map(|ty| ty.to_rocq()).collect_vec(),
                }),
            ]),
            Expr::GetAssociatedFunction {
                ty,
                func,
                generic_consts,
                generic_tys,
            } => rocq::Expression::just_name("M.get_associated_function").monadic_apply_many(&[
                ty.to_rocq(),
                Rc::new(rocq::Expression::String(func.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: generic_consts
                        .iter()
                        .map(|generic_const| generic_const.to_rocq())
                        .collect(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: generic_tys
                        .iter()
                        .map(|generic_ty| generic_ty.to_rocq())
                        .collect(),
                }),
            ]),
            Expr::Literal(literal) => literal.to_rocq(),
            Expr::ConstructorAsClosure {
                path,
                generic_consts,
                generic_tys,
            } => rocq::Expression::just_name("M.constructor_as_closure").apply_many(&[
                Rc::new(rocq::Expression::String(path.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: generic_consts
                        .iter()
                        .map(|generic_const| generic_const.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: generic_tys
                        .iter()
                        .map(|generic_ty| generic_ty.to_rocq())
                        .collect_vec(),
                }),
            ]),
            Expr::Call { func, args, kind } => match kind {
                CallKind::Pure => func
                    .to_rocq()
                    .apply_many(&args.iter().map(|arg| arg.to_rocq()).collect_vec()),
                CallKind::Effectful => func
                    .to_rocq()
                    .monadic_apply_many(&args.iter().map(|arg| arg.to_rocq()).collect_vec()),
                CallKind::Closure(ty) => rocq::Expression::just_name("M.call_closure")
                    .monadic_apply_many(&[
                        ty.to_rocq(),
                        func.to_rocq(),
                        Rc::new(rocq::Expression::List {
                            exprs: args.iter().map(|arg| arg.to_rocq()).collect_vec(),
                        }),
                    ]),
            },
            Expr::CallTy { func, ty } => func.to_rocq().apply(ty.to_rocq()),
            Expr::Alloc { ty, expr } => rocq::Expression::just_name("M.alloc")
                .monadic_apply_many(&[ty.to_rocq(), expr.to_rocq()]),
            Expr::LogicalOperator { name, lhs, rhs } => rocq::Expression::just_name(name.as_str())
                .monadic_apply_many(&[lhs.to_rocq(), rocq::Expression::monadic(rhs.to_rocq())]),
            Expr::Cast { target_ty, source } => rocq::Expression::just_name("M.cast")
                .apply_many(&[target_ty.to_rocq(), source.to_rocq()]),
            Expr::Lambda {
                args,
                body,
                is_for_match: _,
                form,
            } => match form {
                LambdaForm::Function => Rc::new(rocq::Expression::Function {
                    parameters: args
                        .iter()
                        .map(|(name, _)| rocq::Expression::just_name(name))
                        .collect_vec(),
                    body: rocq::Expression::monadic(body.to_rocq()),
                }),
                _ => {
                    let body = Rc::new(rocq::Expression::Function {
                        parameters: vec![rocq::Expression::just_name("γ")],
                        body: rocq::Expression::monadic(Rc::new(rocq::Expression::Match {
                            scrutinees: vec![rocq::Expression::just_name("γ")],
                            arms: vec![
                                (
                                    vec![Rc::new(rocq::Expression::List {
                                        exprs: args
                                            .iter()
                                            .map(|(name, _)| rocq::Expression::name_pattern(name))
                                            .collect(),
                                    })],
                                    rocq::Expression::monadic(body.to_rocq()),
                                ),
                                (
                                    vec![Rc::new(rocq::Expression::Wild)],
                                    rocq::Expression::just_name("M.impossible").apply(Rc::new(
                                        rocq::Expression::String(
                                            "wrong number of arguments".to_string(),
                                        ),
                                    )),
                                ),
                            ],
                        })),
                    });
                    if matches!(form, LambdaForm::Closure) {
                        return rocq::Expression::just_name("M.closure").apply(body);
                    }
                    body
                }
            },
            Expr::Array {
                elements,
                is_internal,
            } => {
                let elements_expression = Rc::new(rocq::Expression::List {
                    exprs: elements
                        .iter()
                        .map(|element| element.to_rocq())
                        .collect_vec(),
                });

                if *is_internal {
                    return elements_expression;
                }

                rocq::Expression::just_name("Value.Array").apply(elements_expression)
            }
            Expr::Tuple { elements } => {
                rocq::Expression::just_name("Value.Tuple").apply(Rc::new(rocq::Expression::List {
                    exprs: elements
                        .iter()
                        .map(|element| element.to_rocq())
                        .collect_vec(),
                }))
            }
            Expr::Let {
                name,
                ty,
                init,
                body,
            } => Rc::new(rocq::Expression::Let {
                suffix: if ty.is_some() {
                    "~".to_string()
                } else {
                    "".to_string()
                },
                name: name.to_owned(),
                ty: ty.as_ref().map(|ty| ty.to_rocq()),
                init: init.to_rocq(),
                body: body.to_rocq(),
            }),
            Expr::Match {
                ty,
                scrutinee,
                arms,
            } => rocq::Expression::just_name("M.match_operator").monadic_apply_many(&[
                ty.to_rocq(),
                scrutinee.to_rocq(),
                Rc::new(rocq::Expression::List {
                    exprs: arms.iter().map(|arm| arm.to_rocq()).collect(),
                }),
            ]),
            Expr::PointerCoercion {
                coercion,
                source_ty,
                target_ty,
            } => rocq::Expression::just_name("M.pointer_coercion").apply_many(&[
                coercion.to_rocq(),
                source_ty.to_rocq(),
                target_ty.to_rocq(),
            ]),
            Expr::Loop { ty, body } => rocq::Expression::just_name("M.loop")
                .monadic_apply_many(&[ty.to_rocq(), rocq::Expression::monadic(body.to_rocq())]),
            Expr::Index { base, index } => {
                rocq::Expression::just_name("M.SubPointer.get_array_field")
                    .monadic_apply_many(&[base.to_rocq(), index.to_rocq()])
            }
            Expr::ControlFlow(lcf_expression) => lcf_expression.to_rocq(),
            Expr::StructStruct {
                path,
                arg_consts,
                arg_tys,
                fields,
                base,
            } => match base {
                None => rocq::Expression::just_name("Value.mkStructRecord").apply_many(&[
                    Rc::new(rocq::Expression::String(path.to_string())),
                    Rc::new(rocq::Expression::List {
                        exprs: arg_consts
                            .iter()
                            .map(|arg_const| arg_const.to_rocq())
                            .collect_vec(),
                    }),
                    Rc::new(rocq::Expression::List {
                        exprs: arg_tys.iter().map(|arg_ty| arg_ty.to_rocq()).collect_vec(),
                    }),
                    Rc::new(rocq::Expression::List {
                        exprs: fields
                            .iter()
                            .map(|(name, expr)| {
                                Rc::new(rocq::Expression::Tuple(vec![
                                    Rc::new(rocq::Expression::String(name.to_owned())),
                                    expr.to_rocq(),
                                ]))
                            })
                            .collect_vec(),
                    }),
                ]),
                Some(base) => rocq::Expression::just_name("M.struct_record_update").apply_many(&[
                    base.to_rocq(),
                    Rc::new(rocq::Expression::List {
                        exprs: fields
                            .iter()
                            .map(|(name, expr)| {
                                Rc::new(rocq::Expression::Tuple(vec![
                                    Rc::new(rocq::Expression::String(name.to_string())),
                                    expr.to_rocq(),
                                ]))
                            })
                            .collect(),
                    }),
                ]),
            },
            Expr::StructTuple {
                path,
                arg_consts,
                arg_tys,
                fields,
            } => rocq::Expression::just_name("Value.StructTuple").apply_many(&[
                Rc::new(rocq::Expression::String(path.to_string())),
                Rc::new(rocq::Expression::List {
                    exprs: arg_consts
                        .iter()
                        .map(|arg_const| arg_const.to_rocq())
                        .collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: arg_tys.iter().map(|arg_ty| arg_ty.to_rocq()).collect_vec(),
                }),
                Rc::new(rocq::Expression::List {
                    exprs: fields.iter().map(|expr| expr.to_rocq()).collect(),
                }),
            ]),
            Expr::Use(expr) => rocq::Expression::just_name("M.use").apply(expr.to_rocq()),
            Expr::InternalString(s) => Rc::new(rocq::Expression::String(s.to_string())),
            Expr::InternalInteger(i) => rocq::Expression::just_name(i.to_string().as_str()),
            Expr::Return(value) => {
                rocq::Expression::just_name("M.return_").monadic_apply(value.to_rocq())
            }
            Expr::Comment(message, expr) => Rc::new(rocq::Expression::Comment(
                message.to_owned(),
                expr.to_rocq(),
            )),
            Expr::Ty(ty) => ty.to_rocq(),
        }
    }

    pub(crate) fn to_name(&self) -> String {
        match self {
            Expr::LocalVar(name) => name.clone(),
            Expr::Literal(literal) => literal.to_name(),
            _ => "expr".to_string(),
        }
    }
}
