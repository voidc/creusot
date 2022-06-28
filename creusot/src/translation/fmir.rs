use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{Place, BasicBlock, BinOp}, ty::{subst::SubstsRef, AdtDef}};
use rustc_span::Symbol;
use rustc_target::abi::VariantIdx;

enum Statement<'tcx> {
  Assignment(Place<'tcx>, Expr<'tcx>),
  Resolve(Place<'tcx>),
  Assertion(Expr<'tcx>),
  Invariant(Symbol, Expr<'tcx>),
}

enum Expr<'tcx> {
  Place(Place<'tcx>),
  BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
  Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
  BorrowMut(Place<'tcx>),
  Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
}

enum Terminator<'tcx> {
  Goto(BasicBlock),
  Switch(Place<'tcx>, Vec<(Pattern<'tcx>, BasicBlock)>),
}

enum Pattern<'tcx> {
    Constructor { adt: AdtDef<'tcx>, variant: VariantIdx, fields: Vec<Pattern<'tcx>> },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard,
    Binder(String),
    Boolean(bool),
}