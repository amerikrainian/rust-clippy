use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::sugg::Sugg;
use clippy_utils::visitors::{Descend, for_each_expr_without_closures};
use clippy_utils::{SpanlessEq, is_integer_literal};
use rustc_ast::{LitIntType, LitKind};
use rustc_errors::{Applicability, MultiSpan};
use rustc_hir::{BinOpKind, Block, Expr, ExprKind, UnOp};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty;
use rustc_session::declare_lint_pass;
use rustc_span::source_map::Spanned;
use std::ops::ControlFlow;

declare_clippy_lint! {
    /// ### What it does
    /// Detects manual zero checks before dividing integers, such as `if x != 0 { y / x }`.
    ///
    /// ### Why is this bad?
    /// `checked_div` already handles the zero case and makes the intent clearer while avoiding a
    /// panic from a manual division.
    ///
    /// ### Example
    /// ```no_run
    /// # let (a, b) = (10u32, 5u32);
    /// if b != 0 {
    ///     let result = a / b;
    ///     println!("{result}");
    /// }
    /// ```
    /// Use instead:
    /// ```no_run
    /// # let (a, b) = (10u32, 5u32);
    /// if let Some(result) = a.checked_div(b) {
    ///     println!("{result}");
    /// }
    /// ```
    #[clippy::version = "1.93.0"]
    pub MANUAL_CHECKED_DIV,
    nursery,
    "manual zero checks before dividing integers"
}
declare_lint_pass!(ManualCheckedDiv => [MANUAL_CHECKED_DIV]);

#[derive(Copy, Clone)]
enum NonZeroBranch {
    Then,
    Else,
}

impl LateLintPass<'_> for ManualCheckedDiv {
    fn check_expr(&mut self, cx: &LateContext<'_>, expr: &Expr<'_>) {
        if let ExprKind::If(cond, then, r#else) = expr.kind
            && !expr.span.from_expansion()
            && let Some((divisor, branch)) = divisor_from_condition(cond)
            && is_integer(cx, divisor)
            && let Some(block) = branch_block(then, r#else, branch)
        {
            let mut eq = SpanlessEq::new(cx).deny_side_effects().paths_by_resolution();
            if !eq.eq_expr(divisor, divisor) {
                return;
            }

            let mut applicability = Applicability::MaybeIncorrect;
            let mut divisions = Vec::new();
            let mut first_use = None;

            let found_early_use = for_each_expr_without_closures(block, |e| {
                if let ExprKind::Binary(binop, lhs, rhs) = e.kind
                    && binop.node == BinOpKind::Div
                    && eq.eq_expr(rhs, divisor)
                    && is_integer(cx, lhs)
                {
                    match first_use {
                        None => first_use = Some(UseKind::Division),
                        Some(UseKind::Other) => return ControlFlow::Break(()),
                        Some(UseKind::Division) => {},
                    }

                    let lhs_snip = Sugg::hir_with_applicability(cx, lhs, "_", &mut applicability);
                    let rhs_snip = Sugg::hir_with_applicability(cx, rhs, "_", &mut applicability);
                    let lhs_ty = cx.typeck_results().expr_ty(lhs);
                    let lhs_sugg = lhs_snip.maybe_paren().to_string();
                    let type_suffix = if matches!(
                        lhs.kind,
                        ExprKind::Lit(Spanned {
                            node: LitKind::Int(_, LitIntType::Unsuffixed),
                            ..
                        }) | ExprKind::Unary(
                            UnOp::Neg,
                            Expr {
                                kind: ExprKind::Lit(Spanned {
                                    node: LitKind::Int(_, LitIntType::Unsuffixed),
                                    ..
                                }),
                                ..
                            }
                        )
                    ) {
                        format!("_{lhs_ty}")
                    } else {
                        String::new()
                    };
                    let suggestion = format!("{lhs_sugg}{type_suffix}.checked_div({rhs_snip})");
                    divisions.push((e.span, suggestion));

                    ControlFlow::<(), _>::Continue(Descend::No)
                } else if eq.eq_expr(e, divisor) {
                    if first_use.is_none() {
                        first_use = Some(UseKind::Other);
                    }
                    ControlFlow::<(), _>::Continue(Descend::Yes)
                } else {
                    ControlFlow::<(), _>::Continue(Descend::Yes)
                }
            });

            if found_early_use.is_some() || first_use != Some(UseKind::Division) || divisions.is_empty() {
                return;
            }

            let mut spans: Vec<_> = divisions.iter().map(|(span, _)| *span).collect();
            spans.push(cond.span);
            span_lint_and_then(
                cx,
                MANUAL_CHECKED_DIV,
                MultiSpan::from_spans(spans),
                "manual checked division",
                |diag| {
                    diag.multipart_suggestion("consider using `checked_div`", divisions, applicability);
                },
            );
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum UseKind {
    Division,
    Other,
}

fn divisor_from_condition<'tcx>(cond: &'tcx Expr<'tcx>) -> Option<(&'tcx Expr<'tcx>, NonZeroBranch)> {
    let ExprKind::Binary(binop, lhs, rhs) = cond.kind else {
        return None;
    };

    match binop.node {
        BinOpKind::Ne | BinOpKind::Lt if is_zero(lhs) => Some((rhs, NonZeroBranch::Then)),
        BinOpKind::Ne | BinOpKind::Gt if is_zero(rhs) => Some((lhs, NonZeroBranch::Then)),
        BinOpKind::Eq if is_zero(lhs) => Some((rhs, NonZeroBranch::Else)),
        BinOpKind::Eq if is_zero(rhs) => Some((lhs, NonZeroBranch::Else)),
        _ => None,
    }
}

fn branch_block<'tcx>(
    then: &'tcx Expr<'tcx>,
    r#else: Option<&'tcx Expr<'tcx>>,
    branch: NonZeroBranch,
) -> Option<&'tcx Block<'tcx>> {
    match branch {
        NonZeroBranch::Then => match then.kind {
            ExprKind::Block(block, _) => Some(block),
            _ => None,
        },
        NonZeroBranch::Else => match r#else?.kind {
            ExprKind::Block(block, _) => Some(block),
            _ => None,
        },
    }
}

fn is_zero(expr: &Expr<'_>) -> bool {
    is_integer_literal(expr, 0)
}

fn is_integer(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    matches!(
        cx.typeck_results().expr_ty(expr).peel_refs().kind(),
        ty::Uint(_) | ty::Int(_)
    )
}
