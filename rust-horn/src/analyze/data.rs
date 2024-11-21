use indexmap::IndexMap;
use rustc_hash::FxHashSet;

use crate::types::{
    BasicBlock, BorrowKind, ConstOperand, DefId, FieldDef, FieldIdx, Float128, Float16, Float32,
    Float64, FloatTy, GenericArgsRef, Local, MirBinOp, MirBody, MirUnOp, Operand, ParamEnv, Place,
    ProjectionElem, RhTyKind, Rvalue, Size, TransparentKind, Ty, TyCtxt, TyKind, VariantIdx,
    DUMMY_SP,
};
use crate::util::{FLD0, FLD1, VRT0};

#[derive(Copy, Clone)]
/// Access to the MIR and the type context.
pub struct MirAccess<'steal, 'tcx> {
    pub mir: &'steal MirBody<'tcx>,
    pub tcx: TyCtxt<'tcx>,
}
impl<'tcx> MirAccess<'_, 'tcx> {
    pub fn get_bool(self) -> Ty<'tcx> { Ty::new(self.tcx.types.bool) }
}

pub trait GetTypeExt<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'_, 'tcx>) -> Ty<'tcx>;
}

impl<'tcx> GetTypeExt<'tcx> for Local {
    fn get_ty(&self, mir_access: MirAccess<'_, 'tcx>) -> Ty<'tcx> {
        let local = *self;
        let MirAccess { mir, .. } = mir_access;
        Ty::new(mir.local_decls[local].ty)
    }
}

impl<'tcx> GetTypeExt<'tcx> for Place<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'_, 'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx).ty)
    }
}

impl<'tcx> GetTypeExt<'tcx> for Operand<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'_, 'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx))
    }
}

impl<'tcx> GetTypeExt<'tcx> for Rvalue<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'_, 'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx))
    }
}

pub trait MirAccessCtxExt<'tcx> {
    type Context;
    fn get_ty_with(&self, mir_access: MirAccess<'_, 'tcx>, context: Self::Context) -> Ty<'tcx>;
}

impl<'tcx> MirAccessCtxExt<'tcx> for Place<'tcx> {
    type Context = usize;

    fn get_ty_with(&self, mir_access: MirAccess<'_, 'tcx>, i: Self::Context) -> Ty<'tcx> {
        let MirAccess { mir, tcx } = mir_access;
        Ty::new(Place::ty_from(self.local, &self.projection[0..i], mir, tcx).ty)
    }
}

impl<'tcx> MirAccessCtxExt<'tcx> for FieldDef {
    type Context = GenericArgsRef<'tcx>;

    fn get_ty_with(&self, mir_access: MirAccess<'_, 'tcx>, adt_substs: Self::Context) -> Ty<'tcx> {
        let MirAccess { tcx, .. } = mir_access;
        Ty::new(self.ty(tcx, adt_substs))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Basically `Var`iables need to be unique.
pub enum Var {
    /// Input variable of a basic block, and argument of a predicate.
    Input {
        /// Corresponding `Local` in the MIR.
        local: Local,
    },
    /// Result of the function. Called `res` in the paper.
    SelfResult,
    /// Does the function get `panic!`ked?
    SelfPanic,
    CallResult {
        /// `BasicBlock` of the `Call` instruction
        caller: BasicBlock,
    },
    #[allow(dead_code)]
    CallIdent {
        /// Unique identifier of an Ident in the inlined *function*.
        identifier: u32,
        /// `BasicBlock` of the `Call` instruction
        caller: BasicBlock,
    },
    Rand {
        /// `BasicBlock` of the `Call` instruction
        caller: BasicBlock,
    },
    /// Logic variable (prophecy) for a mutable reference.
    MutRet {
        location: BasicBlock,
        stmt_index: usize,
    },
    Split(BasicBlock, VariantIdx, FieldIdx),
    /// Uninitialized value.
    Uninit,
}

#[derive(Debug, Clone)]
pub enum Path<'tcx> {
    Var(Var, Ty<'tcx>),
    Proj {
        projection: Proj<'tcx>,
        body: Box<Self>,
    },
}

impl<'tcx> Path<'tcx> {
    fn ty(&self) -> Ty<'tcx> {
        match self {
            Path::Var(_, ty)
            | Path::Proj {
                projection: Proj { base_ty: ty, .. },
                ..
            } => ty.clone(),
        }
    }
    pub fn get_proj(
        &self,
        ty: &Ty<'tcx>,
        variant_index: VariantIdx,
        field_index: FieldIdx,
    ) -> Self {
        match self {
            Path::Var(Var::Uninit, _) => self.clone(),
            _ => Path::Proj {
                projection: Proj {
                    base_ty: ty.clone(),
                    variant_index,
                    field_index,
                },
                body: Box::new(self.clone()),
            },
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Const {
    Bool(bool),
    Int(Int),
    Decimal(Float),
    Unit,
}

#[derive(Debug, Copy, Clone)]
pub enum Int {
    Int(i128),
    Uint(u128),
}

#[derive(Debug, Copy, Clone)]
pub enum Float {
    F16(Float16),
    F32(Float32),
    F64(Float64),
    F128(Float128),
}

impl Const {
    pub fn from_mir_constant<'tcx>(c: &ConstOperand<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let evaluated_const_value = || c.const_.eval(tcx, ParamEnv::reveal_all(), DUMMY_SP);
        let ty = c.ty();
        if ty.is_integral() {
            let scalar = evaluated_const_value().unwrap().try_to_scalar().unwrap();
            let bit_width = match ty.kind() {
                TyKind::Int(int_ty) => int_ty.bit_width(),
                TyKind::Uint(uint_ty) => uint_ty.bit_width(),
                _ => unreachable!("typeck should have finished"),
            };
            let int = if let Some(bit_width) = bit_width {
                let sz = Size::from_bits(bit_width);
                let bits = scalar.to_bits(sz).expect("size mismatch");
                if ty.is_signed() {
                    Int::Int(sz.sign_extend(bits))
                } else {
                    Int::Uint(bits)
                }
            } else if ty.is_signed() {
                Int::Int(i128::from(scalar.to_target_isize(&tcx).unwrap()))
            } else {
                Int::Uint(u128::from(scalar.to_target_usize(&tcx).unwrap()))
            };
            Const::Int(int)
        } else if ty.is_floating_point() {
            let scalar = evaluated_const_value().unwrap().try_to_scalar().unwrap();
            let float = match ty.kind() {
                TyKind::Float(float_ty) => match float_ty {
                    FloatTy::F16 => Float::F16(scalar.to_f16().unwrap()),
                    FloatTy::F32 => Float::F32(scalar.to_f32().unwrap()),
                    FloatTy::F64 => Float::F64(scalar.to_f64().unwrap()),
                    FloatTy::F128 => Float::F128(scalar.to_f128().unwrap()),
                },
                _ => unreachable!("typeck should have finished"),
            };
            Const::Decimal(float)
        } else if ty.is_bool() {
            Const::Bool(
                evaluated_const_value()
                    .unwrap()
                    .try_to_scalar()
                    .unwrap()
                    .to_bool()
                    .unwrap(),
            )
        } else if ty.is_unit() {
            Const::Unit
        } else {
            panic!("unexpected type of constant {ty:?}")
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BinOp {
    Add,
    AddWithOverflow,
    Sub,
    SubWithOverflow,
    Mul,
    MulWithOverflow,
    DivInt,
    Mod,
    DivReal,
    And,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

impl BinOp {
    fn from_mir_bin_op(mir_bin_op: MirBinOp, ty: Ty) -> Self {
        match mir_bin_op {
            MirBinOp::Add | MirBinOp::AddUnchecked => BinOp::Add,
            MirBinOp::AddWithOverflow => BinOp::AddWithOverflow,
            MirBinOp::Sub | MirBinOp::SubUnchecked => BinOp::Sub,
            MirBinOp::SubWithOverflow => BinOp::SubWithOverflow,
            MirBinOp::Mul | MirBinOp::MulUnchecked => BinOp::Mul,
            MirBinOp::MulWithOverflow => BinOp::MulWithOverflow,
            MirBinOp::Div => match ty.kind() {
                RhTyKind::Int => BinOp::DivInt,
                RhTyKind::Float => BinOp::DivReal,
                _ => panic!("unexpected type {ty} for division"),
            },
            MirBinOp::Rem => BinOp::Mod,
            MirBinOp::BitAnd => BinOp::And,
            MirBinOp::Eq => BinOp::Eq,
            MirBinOp::Lt => BinOp::Lt,
            MirBinOp::Le => BinOp::Le,
            MirBinOp::Ne => BinOp::Ne,
            MirBinOp::Ge => BinOp::Ge,
            MirBinOp::Gt => BinOp::Gt,
            _ => panic!("unsupported binary operator {mir_bin_op:?}"),
        }
    }
    pub fn is_overflow_kind(self) -> bool {
        matches!(
            self,
            Self::AddWithOverflow | Self::SubWithOverflow | Self::MulWithOverflow
        )
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    Abs,
}
impl UnOp {
    pub fn from_mir_un_op(mir_un_op: MirUnOp) -> Self {
        match mir_un_op {
            MirUnOp::Not => Self::Not,
            MirUnOp::Neg => Self::Neg,
            MirUnOp::PtrMetadata => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'tcx> {
    Path(Path<'tcx>),
    Const(Const),
    BinOp(BinOp, Box<Self>, Box<Self>),
    UnOp(UnOp, Box<Self>),
    /// Same as `Aggregate` in Rust MIR.
    Aggregate {
        ty: Ty<'tcx>,
        variant_index: VariantIdx,
        fields: Vec<Self>,
    },
    #[allow(dead_code)]
    Construct {
        name: &'static str,
        args: Vec<Self>,
    },
}

impl<'tcx> Expr<'tcx> {
    pub fn from_var(var: Var, ty: Ty<'tcx>) -> Self { Expr::Path(Path::Var(var, ty)) }
    /// Create an uninitialized expression. This is used to represent moved variables, dropped variables, and uninitialized variables.
    pub fn uninit(ty: Ty<'tcx>) -> Self { Self::from_var(Var::Uninit, ty) }

    pub fn from_bin_op(bin_op: BinOp, expr1: Self, expr2: Self) -> Self {
        match bin_op {
            BinOp::Ne => Expr::UnOp(
                UnOp::Not,
                Box::new(Expr::BinOp(BinOp::Eq, Box::new(expr1), Box::new(expr2))),
            ),
            _ => Expr::BinOp(bin_op, Box::new(expr1), Box::new(expr2)),
        }
    }

    /// Construct a pair of expressions.
    pub fn pair(ty: Ty<'tcx>, (fst, snd): (Self, Self)) -> Self {
        Expr::Aggregate {
            ty,
            variant_index: VRT0,
            fields: vec![fst, snd],
        }
    }

    fn aggregate_proj(
        base_ty: Ty<'tcx>,
        variant_index: VariantIdx,
        path: &Path<'tcx>,
    ) -> Expr<'tcx> {
        fn get_n_fields(base_ty: &Ty, variant_index: VariantIdx) -> usize {
            match base_ty.kind() {
                RhTyKind::RefMut { .. } => 2,
                RhTyKind::Adt { def: adt_def, .. } => {
                    assert!(variant_index.index() < adt_def.variants().len());
                    adt_def.variants()[variant_index].fields.len()
                }
                RhTyKind::Tuple { elems } => elems.len(),
                _ => unreachable!("unexpected type {base_ty} for projection"),
            }
        }

        Expr::Aggregate {
            variant_index,
            fields: (0..get_n_fields(&base_ty, variant_index))
                .map(|i| Expr::Path(path.get_proj(&base_ty, variant_index, FieldIdx::from(i))))
                .collect(),
            ty: base_ty,
        }
    }
    #[inline]
    fn as_mut_aggregate_fields(&mut self) -> Option<&mut Vec<Expr<'tcx>>> {
        match self {
            Expr::Aggregate { fields, .. } => Some(fields),
            _ => None,
        }
    }

    #[inline]
    pub fn replace(&mut self, other: Self) -> Self { std::mem::replace(self, other) }

    /// Borrow `self` mutably. Returns an `Expr` representing the mutable reference.
    #[inline]
    pub fn do_borrow_mut(
        &mut self,
        body_ty: Ty<'tcx>,
        ref_ty: Ty<'tcx>,
        (location, stmt_index): (BasicBlock, usize),
    ) -> Expr<'tcx> {
        let var = Var::MutRet {
            location,
            stmt_index,
        };
        let mut_ret = Expr::from_var(var, body_ty);
        let mut_cur = self.replace(mut_ret.clone());
        Expr::pair(ref_ty, (mut_cur, mut_ret))
    }
}

impl<'tcx> Expr<'tcx> {
    pub fn decompose_mut_path(path: &Path<'tcx>) -> (Self, Self) {
        let ty = path.ty();
        assert!(
            ty.is_ref_mut(),
            "unexpected type {ty:?} for a mutable reference",
        );
        (
            Expr::Path(path.get_proj(&ty, VRT0, FLD0)),
            Expr::Path(path.get_proj(&ty, VRT0, FLD1)),
        )
    }
    pub fn decompose_mut(self) -> (Self, Self) {
        match self {
            Expr::Path(path) => Self::decompose_mut_path(&path),
            Expr::Aggregate {
                variant_index: VRT0,
                fields: mut xx_,
                ..
            } if xx_.len() == 2 => {
                let x_ = xx_.pop().unwrap();
                let x = xx_.pop().unwrap();
                (x, x_)
            }
            _ => panic!("unexpected expression {self:?} for a mutable reference"),
        }
    }
}

pub type Env<'tcx> = IndexMap<Local, Expr<'tcx>>;

#[derive(Debug, Clone)]
pub struct Proj<'tcx> {
    pub base_ty: Ty<'tcx>,
    pub variant_index: VariantIdx,
    pub field_index: FieldIdx,
}
#[derive(Debug)]
struct Site<'tcx> {
    local: Local,
    projs: Vec<Proj<'tcx>>,
}

impl<'tcx> Site<'tcx> {
    fn from_place(place: &Place<'tcx>, mir_access: MirAccess<'_, 'tcx>) -> Self {
        let Place { local, projection } = place;
        let mut projs = Vec::<Proj>::new();
        let mut variant_index = VRT0;
        for (i, proj) in projection.iter().enumerate() {
            let mut next_variant_index = VRT0;
            let base_ty = place.get_ty_with(mir_access, i);
            match proj {
                ProjectionElem::Deref => match base_ty.kind() {
                    RhTyKind::Transparent { .. } => {}
                    RhTyKind::RefMut { .. } => {
                        projs.push(Proj {
                            variant_index: VRT0,
                            field_index: FLD0,
                            base_ty,
                        });
                    }
                    _ => panic!("unexpected type {base_ty} for dereference"),
                },
                ProjectionElem::Downcast(_, variant_index) => {
                    next_variant_index = variant_index;
                }
                ProjectionElem::Field(field_index, _) => {
                    match base_ty.kind() {
                        RhTyKind::Adt { def, .. } => assert!(
                            variant_index.index() < def.variants().len()
                                && field_index.index() < def.variants()[variant_index].fields.len()
                        ),
                        RhTyKind::Tuple { elems } => {
                            assert!(variant_index == VRT0 && field_index.index() < elems.len());
                        }
                        _ => panic!("unexpected type {base_ty} for taking a field"),
                    };
                    projs.push(Proj {
                        variant_index,
                        field_index,
                        base_ty,
                    });
                }
                _ => panic!("unsupported projection element {proj:?}"),
            }
            variant_index = next_variant_index;
        }
        Site {
            local: *local,
            projs,
        }
    }
}

pub trait ReadExprExt<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'_, 'tcx>) -> Expr<'tcx>;
}

impl<'tcx> ReadExprExt<'tcx> for Place<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'_, 'tcx>) -> Expr<'tcx> {
        let Site { local, projs } = Site::from_place(self, mir_access);
        let mut expr = match env.get(&local) {
            None => Expr::uninit(self.get_ty(mir_access)),
            Some(expr) => expr.clone(),
        };
        for Proj {
            base_ty,
            variant_index,
            field_index,
        } in projs
        {
            expr = match expr {
                Expr::Path(path) => Expr::Path(path.get_proj(&base_ty, variant_index, field_index)),
                Expr::Aggregate {
                    variant_index: variant_index2,
                    mut fields,
                    ..
                } => {
                    assert!(variant_index == variant_index2);
                    fields.remove(field_index.index())
                }
                _ => panic!("unexpected expr {expr:?}"),
            }
        }
        expr
    }
}

pub trait ReadExprMutExt<'tcx> {
    fn get_mut_expr<'env>(
        &self,
        env: &'env mut Env<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
    ) -> &'env mut Expr<'tcx>;
}

impl<'tcx> ReadExprMutExt<'tcx> for Place<'tcx> {
    fn get_mut_expr<'env>(
        &self,
        env: &'env mut Env<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
    ) -> &'env mut Expr<'tcx> {
        let Site { local, projs } = Site::from_place(self, mir_access);
        let mut expr = env
            .entry(local)
            .or_insert_with(|| Expr::uninit(self.get_ty(mir_access)));
        for Proj {
            base_ty,
            variant_index,
            field_index,
        } in projs
        {
            expr = match expr {
                Expr::Path(path) => {
                    *expr = Expr::aggregate_proj(base_ty, variant_index, path);
                    expr.as_mut_aggregate_fields()
                        .unwrap()
                        .get_mut(field_index.index())
                        .unwrap()
                }
                Expr::Aggregate {
                    variant_index: variant_index2,
                    fields,
                    ..
                } => {
                    assert_eq!(variant_index, *variant_index2);
                    &mut fields[field_index.index()]
                }
                _ => panic!("unexpected expr {expr:?}"),
            }
        }
        expr
    }
}

impl<'tcx> ReadExprExt<'tcx> for Operand<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'_, 'tcx>) -> Expr<'tcx> {
        match self {
            Operand::Copy(place) => place.get_expr(env, mir_access),
            Operand::Move(place) => place
                .get_mut_expr(env, mir_access)
                .replace(Expr::uninit(place.get_ty(mir_access))),
            Operand::Constant(box constant) => {
                Expr::Const(Const::from_mir_constant(constant, mir_access.tcx))
            }
        }
    }
}

pub trait ReadExprCtxExt<'tcx> {
    type Context;
    fn get_expr_at(
        &self,
        context: Self::Context,
        env: &mut Env<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
    ) -> Expr<'tcx>;
}

impl<'tcx> ReadExprCtxExt<'tcx> for Rvalue<'tcx> {
    type Context = (BasicBlock, usize);
    fn get_expr_at(
        &self,
        disambiguator: Self::Context,
        env: &mut Env<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
    ) -> Expr<'tcx> {
        let ty = self.get_ty(mir_access);
        match self {
            Rvalue::Use(opd) => opd.get_expr(env, mir_access),
            Rvalue::Ref(_, BorrowKind::Shared, place) => place.get_expr(env, mir_access),
            Rvalue::Ref(_, BorrowKind::Mut { .. }, referee) => {
                let body_ty = referee.get_ty(mir_access);
                referee
                    .get_mut_expr(env, mir_access)
                    .do_borrow_mut(body_ty, ty, disambiguator)
            }
            Rvalue::BinaryOp(mir_bin_op, box (opd1, opd2)) => {
                let operand_ty = opd1.get_ty(mir_access);
                let bin_op = BinOp::from_mir_bin_op(*mir_bin_op, operand_ty);
                let res = Expr::from_bin_op(
                    bin_op,
                    opd1.get_expr(env, mir_access),
                    opd2.get_expr(env, mir_access),
                );
                if bin_op.is_overflow_kind() {
                    Expr::pair(ty, (res, Expr::Const(Const::Bool(false))))
                } else {
                    res
                }
            }
            Rvalue::UnaryOp(mir_un_op, opd) => Expr::UnOp(
                UnOp::from_mir_un_op(*mir_un_op),
                Box::new(opd.get_expr(env, mir_access)),
            ),
            _ => panic!("unexpected rvalue {self:?}"),
        }
    }
}

pub fn set_tag<'tcx>(
    place: &Place<'tcx>,
    tag: VariantIdx,
    env: &mut Env<'tcx>,
    mir_access: MirAccess<'_, 'tcx>,
) {
    let expr = place.get_mut_expr(env, mir_access);
    let base_ty = place.get_ty(mir_access);
    match expr {
        Expr::Path(path) => {
            *expr = Expr::aggregate_proj(base_ty, tag, path);
        }
        Expr::Aggregate { variant_index, .. } => {
            assert!(tag == *variant_index);
        }
        _ => panic!("unexpected expr {expr:?}"),
    }
}

fn needs_drop<'tcx>(ty: &Ty<'tcx>, mir_access: MirAccess<'_, 'tcx>) -> bool {
    fn needs_drop<'tcx>(
        ty: &Ty<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
        seen: &mut FxHashSet<Ty<'tcx>>,
    ) -> bool {
        match ty.kind() {
            RhTyKind::Bool | RhTyKind::Int | RhTyKind::Float => false,
            RhTyKind::Transparent {
                kind: TransparentKind::Box,
                box ty,
            } => needs_drop(ty, mir_access, seen),
            RhTyKind::Adt { def, args } => {
                if seen.insert(ty.clone()) {
                    def.all_fields().any(|fld_def| {
                        needs_drop(&fld_def.get_ty_with(mir_access, args), mir_access, seen)
                    })
                } else {
                    false
                }
            }
            RhTyKind::RefMut { .. } => true,
            RhTyKind::Transparent {
                kind: TransparentKind::RefImmut,
                ..
            } => false,
            RhTyKind::Tuple { elems } => elems.iter().any(|ty| needs_drop(ty, mir_access, seen)),
            _ => panic!("unsupported type {ty}"),
        }
    }

    needs_drop(ty, mir_access, &mut FxHashSet::default())
}

pub trait DropExt<'tcx> {
    fn do_drop(
        &self,
        of_type: &Ty<'tcx>,
        mir_access: MirAccess<'_, 'tcx>,
        conds: &mut Vec<Cond<'tcx>>,
    );
}

impl<'tcx> DropExt<'tcx> for Path<'tcx> {
    fn do_drop(&self, ty: &Ty<'tcx>, _: MirAccess<'_, 'tcx>, conds: &mut Vec<Cond<'tcx>>) {
        fn drop_path<'tcx>(ty: &Ty<'tcx>, path: &Path<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
            if let Path::Var(Var::Uninit, _) = path {
                return;
            }
            match ty.kind() {
                RhTyKind::RefMut { .. } => {
                    let (cur, ret) = Expr::decompose_mut_path(path);
                    conds.push(Cond::Eq { src: cur, tgt: ret });
                }
                RhTyKind::Adt { .. } => {
                    conds.push(Cond::Drop {
                        ty: ty.clone(),
                        arg: Expr::Path(path.clone()),
                    });
                }
                RhTyKind::Transparent { box ty, .. } => drop_path(ty, path, conds),
                _ => panic!("unexpected type {ty}"),
            }
        }

        drop_path(ty, self, conds);
    }
}

impl<'tcx> DropExt<'tcx> for Expr<'tcx> {
    fn do_drop(&self, ty: &Ty<'tcx>, mir_access: MirAccess<'_, 'tcx>, conds: &mut Vec<Cond<'tcx>>) {
        match self {
            Expr::Path(path) => {
                if needs_drop(ty, mir_access) {
                    path.do_drop(ty, mir_access, conds);
                }
            }
            Expr::Aggregate {
                ty,
                variant_index,
                fields,
            } => match ty.kind() {
                RhTyKind::RefMut { .. } => {
                    let (x, x_) = self.clone().decompose_mut();
                    conds.push(Cond::Eq { tgt: x_, src: x });
                }
                RhTyKind::Adt { def, args } => {
                    assert!(variant_index.index() < def.variants().len());
                    let fld_defs = &def.variants()[*variant_index].fields;
                    assert!(fields.len() == fld_defs.len());
                    for (fld_def, fld) in fld_defs.iter().zip(fields) {
                        fld.do_drop(&fld_def.get_ty_with(mir_access, args), mir_access, conds);
                    }
                }
                RhTyKind::Tuple { elems } => {
                    assert!(fields.len() == elems.len());
                    for (ty, fld) in elems.iter().zip(fields) {
                        fld.do_drop(ty, mir_access, conds);
                    }
                }
                _ => panic!("unexpected type {ty} for aggregation"),
            },
            _ => {}
        };
    }
}

pub trait AssignExt<'tcx> {
    fn assign(
        &self,
        new_expr: Expr<'tcx>,
        env: &mut Env<'tcx>,
        conds: &mut Vec<Cond<'tcx>>,
        mir_access: MirAccess<'_, 'tcx>,
    );
}

impl<'tcx> AssignExt<'tcx> for Place<'tcx> {
    fn assign(
        &self,
        new_expr: Expr<'tcx>,
        env: &mut Env<'tcx>,
        conds: &mut Vec<Cond<'tcx>>,
        mir_access: MirAccess<'_, 'tcx>,
    ) {
        let expr = self.get_mut_expr(env, mir_access);
        let old_expr = expr.replace(new_expr);
        old_expr.do_drop(&self.get_ty(mir_access), mir_access, conds);
    }
}

#[derive(Debug)]
pub enum Cond<'tcx> {
    Drop {
        ty: Ty<'tcx>,
        arg: Expr<'tcx>,
    },
    Eq {
        tgt: Expr<'tcx>,
        src: Expr<'tcx>,
    },
    Neq {
        tgt: Expr<'tcx>,
        srcs: Vec<Expr<'tcx>>,
    },
    CallRustFn {
        fun_id: DefId,
        args: Vec<Expr<'tcx>>,
    },
    #[allow(dead_code)]
    Intrinsic {
        name: &'static str,
        args: Vec<Expr<'tcx>>,
    },
}
#[derive(Debug)]
pub enum End<'tcx> {
    Pivot {
        next_switch: BasicBlock,
        args: Vec<Expr<'tcx>>,
    },
    Return {
        res: Option<Expr<'tcx>>,
    },
    Panic,
    NeverReturn,
}
