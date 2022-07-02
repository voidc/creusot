use super::BodyTranslator;
use crate::translation::fmir::{Branches, Terminator};
use crate::{
    ctx::{CloneMap, TranslationCtx},
    translation::{fmir::Expr, traits},
    util::is_ghost_closure,
};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_infer::{
    infer::{InferCtxt, TyCtxtInferExt},
    traits::{FulfillmentError, Obligation, ObligationCause, TraitEngine},
};
use rustc_middle::mir::{BasicBlockData, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::Ty;
use rustc_middle::{
    mir::{
        self, BasicBlock, Location, Operand, SourceInfo, SwitchTargets, TerminatorKind::*, UnOp,
    },
    ty::{
        self,
        subst::{GenericArgKind, SubstsRef},
        ParamEnv, Predicate,
    },
};
use rustc_span::Span;
use rustc_trait_selection::traits::FulfillmentContext;
use std::collections::HashMap;
use why3::mlcfg::Statement;
use why3::QName;

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> BodyTranslator<'_, '_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            Goto { target } => self.emit_terminator(mk_goto(*target)),
            SwitchInt { discr, targets, .. } => {
                let real_discr =
                    discriminator_for_switch(&self.body.basic_blocks()[location.block])
                        .map(Operand::Move)
                        .unwrap_or_else(|| discr.clone());

                let discriminant = self.translate_operand(&real_discr);
                let switch = make_switch(
                    self.ctx,
                    terminator.source_info,
                    real_discr.ty(self.body, self.tcx),
                    targets,
                    discriminant,
                );

                self.emit_terminator(switch);
            }
            Abort => self.emit_terminator(Terminator::Abort),
            Return => self.emit_terminator(Terminator::Return),
            Unreachable => self.emit_terminator(Terminator::Abort),
            Call { func, args, destination, target, .. } => {
                if target.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(Terminator::Abort);
                    return;
                }

                let (fun_def_id, subst) = func_defid(func).expect("expected call with function");

                if let Some(param) = subst.get(0) &&
                    let GenericArgKind::Type(ty) = param.unpack() &&
                    let Some(def_id) = is_ghost_closure(self.tcx, ty) {
                    let assertion = self.assertions.remove(&def_id).unwrap();
                    let (loc, bb) = (destination, target.unwrap());

                    self.emit_ghost_assign(&loc, assertion);
                    self.emit_terminator(Terminator::Goto(bb));
                    return;
                }

                let predicates = self
                    .ctx
                    .extern_spec(fun_def_id)
                    .map(|p| p.predicates_for(self.tcx, subst))
                    .unwrap_or_else(Vec::new);

                use rustc_trait_selection::traits::error_reporting::InferCtxtExt;
                self.tcx.infer_ctxt().enter(|infcx| {
                    let res = evaluate_additional_predicates(
                        &infcx,
                        predicates,
                        self.param_env(),
                        terminator.source_info.span,
                    );
                    if let Err(errs) = res {
                        let hir_id =
                            self.tcx.hir().local_def_id_to_hir_id(self.def_id.expect_local());
                        let body_id = self.tcx.hir().body_owned_by(hir_id);
                        infcx.report_fulfillment_errors(&errs, Some(body_id), false);
                    }
                });

                let mut func_args: Vec<_> =
                    args.iter().map(|arg| self.translate_operand(arg)).collect();

                if func_args.is_empty() {
                    // We use tuple as a dummy argument for 0-ary functions
                    func_args.push(Expr::Tuple(vec![]))
                }
                let call_exp = if self.is_box_new(fun_def_id) {
                    assert_eq!(func_args.len(), 1);

                    func_args.remove(0)
                } else {
                    let exp = Expr::Call(fun_def_id, subst, func_args);
                    let span = terminator.source_info.span.source_callsite();
                    Expr::Span(span, box exp)
                };

                let (loc, bb) = (destination, target.unwrap());
                self.emit_assignment(&loc, call_exp);
                self.emit_terminator(Terminator::Goto(bb));
            }
            Assert { cond, expected, msg: _, target, cleanup: _ } => {
                let mut ass = self.translate_operand(cond);
                if !expected {
                    ass = Expr::UnaryOp(UnOp::Not, box ass);
                }
                let ass = ass.to_why(self.ctx, self.names, Some(self.body));
                self.emit_statement(Statement::Assert(ass));
                self.emit_terminator(mk_goto(*target))
            }

            FalseEdge { real_target, .. } => self.emit_terminator(mk_goto(*real_target)),

            // TODO: Do we really need to do anything more?
            Drop { target, .. } => self.emit_terminator(mk_goto(*target)),
            FalseUnwind { real_target, .. } => {
                self.emit_terminator(mk_goto(*real_target));
            }
            DropAndReplace { target, place, value, .. } => {
                // Drop
                let ty = place.ty(self.body, self.tcx).ty;
                let pl_exp = self.translate_rplace(place);
                self.resolve_ty(ty).emit(pl_exp, self);

                // Assign
                let rhs = match value {
                    Operand::Move(pl) | Operand::Copy(pl) => Expr::Place(*pl),
                    Operand::Constant(box c) => crate::constant::from_mir_constant(
                        self.param_env(),
                        self.ctx,
                        self.names,
                        c,
                    ),
                };

                self.emit_assignment(place, rhs);

                self.emit_terminator(mk_goto(*target))
            }
            Yield { .. } | GeneratorDrop | InlineAsm { .. } | Resume => {
                unreachable!("{:?}", terminator.kind)
            }
        }
    }

    fn is_box_new(&self, def_id: DefId) -> bool {
        self.tcx.def_path_str(def_id) == "std::boxed::Box::<T>::new"
    }
}

pub fn get_func_name<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
    sp: rustc_span::Span,
) -> QName {
    if let Some(it) = ctx.opt_associated_item(def_id) {
        if let ty::TraitContainer(id) = it.container {
            let params = ctx.param_env(names.self_id);
            let method = traits::resolve_assoc_item_opt(ctx.tcx, params, def_id, subst)
                .expect("could not find instance");

            ctx.translate(id);
            ctx.translate(method.0);

            if !method.0.is_local()
                && !ctx.externs.verified(method.0)
                && ctx.extern_spec(method.0).is_none()
                && ctx.extern_spec(def_id).is_none()
            {
                ctx.warn(sp, "calling an external function with no contract will yield an impossible precondition");
            }

            return names.insert(method.0, method.1).qname(ctx.tcx, method.0);
        }
    }

    if !def_id.is_local() && !(ctx.extern_spec(def_id).is_some() || ctx.externs.verified(def_id)) {
        ctx.warn(
            sp,
            "calling an external function with no contract will yield an impossible precondition",
        );
    }
    ctx.translate(def_id);

    names.insert(def_id, subst).qname(ctx.tcx, def_id)
}

// Try to extract a function defid from an operand
fn func_defid<'tcx>(op: &Operand<'tcx>) -> Option<(DefId, SubstsRef<'tcx>)> {
    let fun_ty = op.constant().unwrap().literal.ty();
    if let ty::TyKind::FnDef(def_id, subst) = fun_ty.kind() {
        Some((*def_id, subst))
    } else {
        None
    }
}

fn evaluate_additional_predicates<'tcx>(
    infcx: &InferCtxt<'_, 'tcx>,
    p: Vec<Predicate<'tcx>>,
    param_env: ParamEnv<'tcx>,
    sp: Span,
) -> Result<(), Vec<FulfillmentError<'tcx>>> {
    let mut fulfill_cx = FulfillmentContext::new();
    for predicate in p {
        let cause = ObligationCause::dummy_with_span(sp);
        let obligation = Obligation { cause, param_env, recursion_depth: 0, predicate };
        // holds &= infcx.predicate_may_hold(&obligation);
        fulfill_cx.register_predicate_obligation(&infcx, obligation);
    }
    let errors = fulfill_cx.select_all_or_error(&infcx);
    if !errors.is_empty() {
        return Err(errors);
    } else {
        return Ok(());
    }
}

// Find the place being discriminated, if there is one
pub fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
    let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
        discr
    } else {
        return None;
    };

    if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
        bbd.statements.last()?.kind
    {
        if discr.place() == Some(pl) {
            Some(real_discr)
        } else {
            None
        }
    } else {
        None
    }
}

pub fn make_switch<'tcx>(
    ctx: &TranslationCtx<'_, 'tcx>,
    si: SourceInfo,
    switch_ty: Ty<'tcx>,
    targets: &SwitchTargets,
    discr: Expr<'tcx>,
) -> Terminator<'tcx> {
    use rustc_type_ir::sty::TyKind;
    match switch_ty.kind() {
        TyKind::Adt(def, _) => {
            let d_to_var: HashMap<_, _> =
                def.discriminants(ctx.tcx).map(|(idx, d)| (d.val, idx)).collect();

            let branches: Vec<_> =
                targets.iter().map(|(disc, tgt)| (d_to_var[&disc], (tgt))).collect();

            Terminator::Switch(discr, Branches::Constructor(*def, branches, targets.otherwise()))
        }
        TyKind::Bool => {
            let branches: (_, _) = targets
                .iter()
                .sorted()
                .map(|tgt| tgt.1)
                .chain(std::iter::once(targets.otherwise()))
                .take(2)
                .collect_tuple()
                .unwrap();

            Terminator::Switch(discr, Branches::Bool(branches.0, branches.1))
        }
        TyKind::Float(_) => {
            ctx.crash_and_error(si.span, "Float patterns are currently unsupported")
        }
        TyKind::Uint(_) => {
            let branches: Vec<(_, BasicBlock)> =
                targets.iter().map(|(val, tgt)| (val, tgt)).collect();
            Terminator::Switch(discr, Branches::Uint(branches, targets.otherwise()))
        }
        TyKind::Int(_) => {
            let branches: Vec<(_, BasicBlock)> =
                targets.iter().map(|(val, tgt)| (val as i128, tgt)).collect();

            Terminator::Switch(discr, Branches::Int(branches, targets.otherwise()))
        }
        _ => unimplemented!(),
    }
}

fn mk_goto<'tcx>(bb: rustc_middle::mir::BasicBlock) -> Terminator<'tcx> {
    Terminator::Goto(bb)
}
