use rustc_middle::ty::TyCtxt;

/// The environment used for the translation steps, holding various state
/// information
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    pub(crate) tcx: TyCtxt<'a>,
    pub(crate) axiomatize: bool,
    pub(crate) hir_scope: Option<rustc_hir::HirId>,
}

/// emits a warning with the given messages
pub(crate) fn emit_warning_with_note(
    env: &Env,
    span: &rustc_span::Span,
    warning_msg: &str,
    note_msg: Option<&str>,
) {
    let mut warn = env
        .tcx
        .sess
        .dcx()
        .struct_span_warn(*span, warning_msg.to_string());

    if let Some(note) = note_msg {
        warn.note(note.to_string());
    }

    warn.emit();
}

impl Env<'_> {
    pub(crate) fn in_scope(&self, level: rustc_middle::thir::LintLevel) -> Self {
        match level {
            rustc_middle::thir::LintLevel::Explicit(id) => Self {
                hir_scope: Some(id),
                ..*self
            },
            rustc_middle::thir::LintLevel::Inherited => *self,
        }
    }

    pub(crate) fn unsupported(
        &self,
        span: rustc_span::Span,
        code: &str,
        feature: &str,
    ) -> std::rc::Rc<crate::expression::Expr> {
        use crate::expression::{CallKind, Expr};
        use std::rc::Rc;
        let owner = self
            .hir_scope
            .map(|id| self.tcx.def_path_str(self.tcx.hir_enclosing_body_owner(id)))
            .unwrap_or_else(|| {
                self.tcx
                    .crate_name(rustc_hir::def_id::LOCAL_CRATE)
                    .to_string()
            });
        let message = format!("[{code}] {feature} in {owner}");
        emit_warning_with_note(
            self,
            &span,
            &message,
            Some("Execution of this expression is unsupported"),
        );
        Rc::new(Expr::Call {
            func: Expr::local_var("M.impossible"),
            args: vec![Rc::new(Expr::InternalString(message))],
            kind: CallKind::Effectful,
        })
    }

    pub(crate) fn labeled_exit(&self) -> bool {
        let Some(rustc_hir::Node::Expr(expr)) = self.hir_scope.map(|id| self.tcx.hir_node(id))
        else {
            return false;
        };
        match expr.kind {
            rustc_hir::ExprKind::Break(dest, _) | rustc_hir::ExprKind::Continue(dest) => {
                dest.label.is_some()
            }
            _ => false,
        }
    }
}
