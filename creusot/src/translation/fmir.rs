use std::collections::HashMap;

use indexmap::IndexMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, BinOp, Body, Place, UnOp},
    ty::{subst::SubstsRef, AdtDef},
};
use rustc_span::Symbol;
use rustc_span::{Span, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use why3::{exp::Pattern, mlcfg::BlockId};

use crate::{
    ctx::{item_name, CloneMap, TranslationCtx},
    translation::{
        binop_to_binop,
        function::{place::translate_rplace_inner, terminator::get_func_name},
        unop_to_unop,
    },
    util::item_qname,
};

use super::specification::typing::{Literal, Term};

pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, Expr<'tcx>),
    Borrow(Place<'tcx>, Expr<'tcx>),
    Resolve(Place<'tcx>),
    Assertion(Term<'tcx>),
    Ghost(Term<'tcx>),
    Invariant(Symbol, Term<'tcx>),
}

pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Literal),
    Tuple(Vec<Expr<'tcx>>),
    Span(Span, Box<Expr<'tcx>>),
    // Migration escape hatch
    Exp(why3::exp::Exp),
}

impl<'tcx> Expr<'tcx> {
    pub fn to_why(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        body: Option<&Body<'tcx>>,
    ) -> why3::exp::Exp {
        use why3::exp::Exp;
        match self {
            Expr::Place(pl) => translate_rplace_inner(
                ctx,
                names,
                body.unwrap(),
                &HashMap::new(),
                pl.local,
                pl.projection,
            ),
            Expr::BinOp(BinOp::BitAnd, l, r) => Exp::BinaryOp(
                why3::exp::BinOp::And,
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::BinOp(op, l, r) => Exp::BinaryOp(
                binop_to_binop(op),
                box l.to_why(ctx, names, body),
                box r.to_why(ctx, names, body),
            ),
            Expr::UnaryOp(op, arg) => {
                Exp::UnaryOp(unop_to_unop(op), box arg.to_why(ctx, names, body))
            }
            Expr::Constructor(id, subst, args) => {
                let args = args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();

                match ctx.def_kind(id) {
                    DefKind::Closure => {
                        let mut cons_name = item_name(ctx.tcx, id);
                        cons_name.capitalize();
                        let ctor = names.insert(id, subst).qname_ident(cons_name);
                        Exp::Constructor { ctor, args }
                    }
                    _ => {
                        let ctor = item_qname(ctx.tcx, id);
                        Exp::Constructor { ctor, args }
                    }
                }
            }
            Expr::Call(id, subst, args) => {
                let args: Vec<_> = args.into_iter().map(|a| a.to_why(ctx, names, body)).collect();
                let fname = get_func_name(ctx, names, id, subst, DUMMY_SP);
                Exp::Call(box Exp::impure_qvar(fname), args)
            }
            Expr::Constant(_) => todo!(),
            Expr::Tuple(f) => {
                Exp::Tuple(f.into_iter().map(|f| f.to_why(ctx, names, body)).collect())
            }
            Expr::Exp(e) => e,
            Expr::Span(sp, e) => {
                let e = e.to_why(ctx, names, body);
                ctx.attach_span(sp, e)
            }
        }
    }
}

pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Expr<'tcx>, Branches<'tcx>),
    Return,
    Abort,
}

pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(AdtDef<'tcx>, Vec<(VariantIdx, BasicBlock)>, BasicBlock),
    Bool(BasicBlock, BasicBlock),
}

impl<'tcx> Terminator<'tcx> {
    pub fn to_why(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        body: Option<&Body<'tcx>>,
    ) -> why3::mlcfg::Terminator {
        use why3::exp::Exp;
        use why3::mlcfg::Terminator::*;
        match self {
            Terminator::Goto(bb) => Goto(BlockId(bb.into())),
            Terminator::Switch(switch, branches) => {
                let discr = switch.to_why(ctx, names, body);
                match branches {
                    Branches::Int(brs, def) => {
                        brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                            Switch(
                                Exp::BinaryOp(
                                    why3::exp::BinOp::Eq,
                                    box discr.clone(),
                                    box Exp::Const(why3::exp::Constant::Int(val, None)),
                                ),
                                vec![
                                    (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                                    (Pattern::mk_false(), acc),
                                ],
                            )
                        })
                    }
                    Branches::Uint(brs, def) => {
                        brs.into_iter().rfold(Goto(BlockId(def.into())), |acc, (val, bb)| {
                            Switch(
                                Exp::BinaryOp(
                                    why3::exp::BinOp::Eq,
                                    box discr.clone(),
                                    box Exp::Const(why3::exp::Constant::Uint(val, None)),
                                ),
                                vec![
                                    (Pattern::mk_true(), Goto(BlockId(bb.into()))),
                                    (Pattern::mk_false(), acc),
                                ],
                            )
                        })
                    }
                    Branches::Constructor(adt, vars, def) => {
                        use crate::util::constructor_qname;
                        let count = adt.variants().len();
                        let brs = vars
                            .into_iter()
                            .map(|(var, bb)| {
                                let variant = &adt.variant(var);
                                let wilds =
                                    variant.fields.iter().map(|_| Pattern::Wildcard).collect();
                                let cons_name = constructor_qname(ctx.tcx, variant);
                                (Pattern::ConsP(cons_name, wilds), Goto(BlockId(bb.into())))
                            })
                            .chain(std::iter::once((Pattern::Wildcard, Goto(BlockId(def.into())))))
                            .take(count);

                        Switch(discr, brs.collect())
                    }
                    Branches::Bool(f, t) => Switch(
                        discr,
                        vec![
                            (Pattern::mk_false(), Goto(BlockId(f.into()))),
                            (Pattern::mk_true(), Goto(BlockId(t.into()))),
                        ],
                    ),
                }
            }
            Terminator::Return => Return,
            Terminator::Abort => Absurd,
        }
    }
}

pub struct Block<'tcx> {
    stmts: Vec<Statement<'tcx>>,
    terminator: Option<Terminator<'tcx>>,
}

impl<'tcx> Block<'tcx> {
    pub fn to_why(self) -> why3::mlcfg::Block {
        todo!()
    }
}

pub struct Builder<'tcx> {
    blocks: IndexMap<BasicBlock, Block<'tcx>>,
    current: Block<'tcx>,
    block_id: BasicBlock,
}

impl<'tcx> Builder<'tcx> {
    pub fn new() -> Self {
        Builder {
            blocks: Default::default(),
            block_id: BasicBlock::MAX,
            current: Block { stmts: Vec::new(), terminator: None },
        }
    }
}
