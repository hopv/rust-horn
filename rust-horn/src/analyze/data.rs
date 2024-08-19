use crate::prettify::pr_fun_name;
use crate::represent::{rep, rep_drop_name};
use crate::types::{
    adt_is_box, BasicBlock, BorrowKind, Constant, ConstantKind, DefId, FieldDef, FieldIdx, Float32,
    Float64, FloatTy, GenericArgsRef, Local, Map, MirBinOp, MirBody, MirUnOp, Mutability, Operand,
    ParamEnv, Place, ProjectionElem, Rvalue, Set, Size, Subst, Ty, TyCtxt, TyKind, VariantIdx,
};
use crate::util::{FLD0, FLD1, VRT0};

#[derive(Copy, Clone)]
pub struct MirAccess<'tcx> {
    pub mir: &'tcx MirBody<'tcx>,
    pub generic_args: GenericArgsRef<'tcx>,
    pub tcx: TyCtxt<'tcx>,
}
impl<'tcx> MirAccess<'tcx> {
    pub fn get_bool(self) -> Ty<'tcx> { Ty::new(self.tcx.mk_ty(TyKind::Bool)) }
}

pub trait GetTypeExt<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx>;
}

impl<'tcx> GetTypeExt<'tcx> for Local {
    fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
        let local = *self;
        let MirAccess { mir, generic_args, tcx } = mir_access;
        Ty::new(mir.local_decls[local].ty.subst(tcx, generic_args))
    }
}

impl<'tcx> GetTypeExt<'tcx> for Place<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, generic_args, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx).ty.subst(tcx, generic_args))
    }
}

impl<'tcx> GetTypeExt<'tcx> for Operand<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, generic_args, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx).subst(tcx, generic_args))
    }
}

impl<'tcx> GetTypeExt<'tcx> for Rvalue<'tcx> {
    fn get_ty(&self, mir_access: MirAccess<'tcx>) -> Ty<'tcx> {
        let MirAccess { mir, generic_args, tcx } = mir_access;
        Ty::new(self.ty(mir, tcx).subst(tcx, generic_args))
    }
}

pub trait MirAccessCtxExt<'tcx> {
    type Context;
    fn get_ty_with(&self, mir_access: MirAccess<'tcx>, context: Self::Context) -> Ty<'tcx>;
}

impl<'tcx> MirAccessCtxExt<'tcx> for Place<'tcx> {
    type Context = usize;

    fn get_ty_with(&self, mir_access: MirAccess<'tcx>, i: Self::Context) -> Ty<'tcx> {
        let MirAccess { mir, generic_args, tcx } = mir_access;
        Ty::new(
            Place::ty_from(self.local, &self.projection[0..i], mir, tcx)
                .ty
                .subst(tcx, generic_args),
        )
    }
}

impl<'tcx> MirAccessCtxExt<'tcx> for FieldDef {
    type Context = GenericArgsRef<'tcx>;

    fn get_ty_with(&self, mir_access: MirAccess<'tcx>, adt_substs: Self::Context) -> Ty<'tcx> {
        let MirAccess { generic_args, tcx, .. } = mir_access;
        Ty::new(self.ty(tcx, adt_substs).subst(tcx, generic_args))
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
    Proj { projection: Proj<'tcx>, body: Box<Self> },
}

impl<'tcx> Path<'tcx> {
    fn ty(&self) -> Ty<'tcx> {
        match self {
            Path::Var(_, ty) | Path::Proj { projection: Proj { base_ty: ty, .. }, .. } => *ty,
        }
    }
    pub fn get_proj(&self, ty: Ty<'tcx>, variant_index: VariantIdx, field_index: FieldIdx) -> Self {
        match self {
            Path::Var(Var::Uninit, _) => self.clone(),
            _ => Path::Proj {
                projection: Proj { base_ty: ty, variant_index, field_index },
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
    F32(Float32),
    F64(Float64),
}

impl Const {
    pub fn from_mir_constant<'tcx>(c: &Constant<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let evaluated_const_value = || match c.literal {
            ConstantKind::Ty(c) => c.val.eval(tcx, ParamEnv::empty()).try_to_value(),
            ConstantKind::Val(val, _) => Some(val),
        };
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
                    #[allow(clippy::cast_possible_wrap)]
                    Int::Int(sz.sign_extend(bits) as i128)
                } else {
                    Int::Uint(bits)
                }
            } else if ty.is_signed() {
                Int::Int(i128::from(scalar.to_machine_isize(&tcx).unwrap()))
            } else {
                Int::Uint(u128::from(scalar.to_machine_usize(&tcx).unwrap()))
            };
            Const::Int(int)
        } else if ty.is_floating_point() {
            let scalar = evaluated_const_value().unwrap().try_to_scalar().unwrap();
            let float = match ty.kind() {
                TyKind::Float(float_ty) => match float_ty {
                    FloatTy::F32 => Float::F32(scalar.to_f32().unwrap()),
                    FloatTy::F64 => Float::F64(scalar.to_f64().unwrap()),
                },
                _ => unreachable!("typeck should have finished"),
            };
            Const::Decimal(float)
        } else if ty.is_bool() {
            Const::Bool(
                evaluated_const_value().unwrap().try_to_scalar().unwrap().to_bool().unwrap(),
            )
        } else if ty.is_unit() {
            Const::Unit
        } else {
            panic!("unexpected type of constant {:?}", ty)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
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
            MirBinOp::Add => BinOp::Add,
            MirBinOp::Sub => BinOp::Sub,
            MirBinOp::Mul => BinOp::Mul,
            MirBinOp::Div => match &ty.kind() {
                TyKind::Int(_) | TyKind::Uint(_) => BinOp::DivInt,
                TyKind::Float(_) => BinOp::DivReal,
                _ => panic!("unexpected type {} for division", ty),
            },
            MirBinOp::Rem => BinOp::Mod,
            MirBinOp::BitAnd => BinOp::And,
            MirBinOp::Eq => BinOp::Eq,
            MirBinOp::Lt => BinOp::Lt,
            MirBinOp::Le => BinOp::Le,
            MirBinOp::Ne => BinOp::Ne,
            MirBinOp::Ge => BinOp::Ge,
            MirBinOp::Gt => BinOp::Gt,
            _ => panic!("unsupported binary operator {:?}", mir_bin_op),
        }
    }

    pub fn try_from_fun(fun: DefId) -> Option<Self> {
        match pr_fun_name(fun).as_str() {
            "<eq>" => Some(BinOp::Eq),
            "<ne>" => Some(BinOp::Ne),
            "<add>" => Some(BinOp::Add),
            "<div-int>" => Some(BinOp::DivInt),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
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
        }
    }
    pub fn try_from_fun(fun: DefId) -> Option<UnOp> {
        match pr_fun_name(fun).as_str() {
            "<abs>" => Some(UnOp::Abs),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'tcx> {
    Path(Path<'tcx>),
    Const(Const),
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnOp(UnOp, Box<Expr<'tcx>>),
    /// Same as `Aggregate` in Rust MIR.
    Aggregate {
        ty: Ty<'tcx>,
        variant_index: VariantIdx,
        fields: Vec<Expr<'tcx>>,
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

    pub fn pair(ty: Ty<'tcx>, (fst, snd): (Self, Self)) -> Self {
        Expr::Aggregate { ty, variant_index: VRT0, fields: vec![fst, snd] }
    }

    fn aggregate_proj(
        base_ty: Ty<'tcx>,
        variant_index: VariantIdx,
        path: &Path<'tcx>,
    ) -> Expr<'tcx> {
        fn get_n_fields(base_ty: Ty, variant_index: VariantIdx) -> usize {
            match &base_ty.kind() {
                TyKind::Ref(_, _, Mutability::Mut) => 2,
                TyKind::Adt(adt_def, _) => {
                    assert!(!adt_def.is_box());
                    assert!(variant_index.index() < adt_def.variants.len());
                    adt_def.variants[variant_index].fields.len()
                }
                TyKind::Tuple(generic_args) => generic_args.types().count(),
                _ => unreachable!("unexpected type {} for projection", base_ty),
            }
        }

        Expr::Aggregate {
            ty: base_ty,
            variant_index,
            fields: (0..get_n_fields(base_ty, variant_index))
                .map(|i| Expr::Path(path.get_proj(base_ty, variant_index, FieldIdx::from(i))))
                .collect(),
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
        let var = Var::MutRet { location, stmt_index };
        let mut_ret = Expr::from_var(var, body_ty);
        let mut_cur = self.replace(mut_ret.clone());
        Expr::pair(ref_ty, (mut_cur, mut_ret))
    }
}

impl Ty<'_> {
    pub fn ty_body(self) -> Self {
        match self.kind() {
            TyKind::Ref(_, ty, Mutability::Not) => return Ty::new(ty).ty_body(),
            TyKind::Adt(adt_def, adt_substs) => {
                if let Some(ty) = adt_is_box(adt_def, adt_substs) {
                    return ty.ty_body();
                }
            }
            _ => (),
        };
        self
    }
}

impl<'tcx> Expr<'tcx> {
    pub fn decompose_mut_path(path: &Path<'tcx>) -> (Self, Self) {
        let ty = path.ty().ty_body();
        assert!(
            matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Mut)),
            "unexpected type {:?} for a mutable reference",
            ty
        );
        (Expr::Path(path.get_proj(ty, VRT0, FLD0)), Expr::Path(path.get_proj(ty, VRT0, FLD1)))
    }
    pub fn decompose_mut(self) -> (Self, Self) {
        match self {
            Expr::Path(path) => Self::decompose_mut_path(&path),
            Expr::Aggregate { variant_index: VRT0, fields: mut xx_, .. } if xx_.len() == 2 => {
                let x_ = xx_.pop().unwrap();
                let x = xx_.pop().unwrap();
                (x, x_)
            }
            _ => panic!("unexpected expression {:?} for a mutable reference", self),
        }
    }
}

pub type Env<'tcx> = Map<Local, Expr<'tcx>>;

#[derive(Debug, Copy, Clone)]
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
    fn from_place(place: &Place<'tcx>, mir_access: MirAccess<'tcx>) -> Self {
        let Place { local, projection } = place;
        let mut projs = Vec::<Proj>::new();
        let mut variant_index = VRT0;
        for (i, proj) in projection.iter().enumerate() {
            let mut next_variant_index = VRT0;
            let base_ty = place.get_ty_with(mir_access, i);
            match &proj {
                ProjectionElem::Deref => match &base_ty.kind() {
                    TyKind::Ref(_, _, Mutability::Not) => {}
                    TyKind::Adt(adt_def, _) if adt_def.is_box() => {}
                    TyKind::Ref(_, _, Mutability::Mut) => {
                        projs.push(Proj { variant_index: VRT0, field_index: FLD0, base_ty });
                    }
                    _ => panic!("unexpected type {} for dereference", base_ty),
                },
                ProjectionElem::Downcast(_, variant_index) => {
                    next_variant_index = *variant_index;
                }
                ProjectionElem::Field(field_index, _) => {
                    match &base_ty.kind() {
                        TyKind::Adt(adt_def, _) => assert!(
                            variant_index.index() < adt_def.variants.len()
                                && field_index.index()
                                    < adt_def.variants[variant_index].fields.len()
                        ),
                        TyKind::Tuple(generic_args) => {
                            assert!(
                                variant_index == VRT0
                                    && field_index.index() < generic_args.types().count()
                            );
                        }
                        _ => panic!("unexpected type {} for taking a field", base_ty),
                    };
                    projs.push(Proj { variant_index, field_index: *field_index, base_ty });
                }
                _ => panic!("unsupported projection element {:?}", proj),
            }
            variant_index = next_variant_index;
        }
        Site { local: *local, projs }
    }
}

pub trait ReadExprExt<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>) -> Expr<'tcx>;
}

impl<'tcx> ReadExprExt<'tcx> for Place<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>) -> Expr<'tcx> {
        let Site { local, projs } = Site::from_place(self, mir_access);
        let mut expr = match env.get(&local) {
            None => Expr::uninit(self.get_ty(mir_access)),
            Some(expr) => expr.clone(),
        };
        for &proj in &projs {
            let Proj { base_ty, variant_index, field_index } = proj;
            expr = match expr {
                Expr::Path(path) => Expr::Path(path.get_proj(base_ty, variant_index, field_index)),
                Expr::Aggregate { variant_index: variant_index2, mut fields, .. } => {
                    assert!(variant_index == variant_index2);
                    fields.remove(field_index.index())
                }
                _ => panic!("unexpected expr {:?}", &expr),
            }
        }
        expr
    }
}

pub trait ReadExprMutExt<'tcx> {
    fn get_mut_expr<'env>(
        &self,
        env: &'env mut Env<'tcx>,
        mir_access: MirAccess<'tcx>,
    ) -> &'env mut Expr<'tcx>;
}

impl<'tcx> ReadExprMutExt<'tcx> for Place<'tcx> {
    fn get_mut_expr<'env>(
        &self,
        env: &'env mut Env<'tcx>,
        mir_access: MirAccess<'tcx>,
    ) -> &'env mut Expr<'tcx> {
        let Site { local, projs } = Site::from_place(self, mir_access);
        let mut expr = env.entry(local).or_insert_with(|| Expr::uninit(self.get_ty(mir_access)));
        for &proj in &projs {
            let Proj { base_ty, variant_index, field_index } = proj;
            expr = match expr {
                Expr::Path(path) => {
                    *expr = Expr::aggregate_proj(base_ty, variant_index, path);
                    expr.as_mut_aggregate_fields().unwrap().get_mut(field_index.index()).unwrap()
                }
                Expr::Aggregate { variant_index: variant_index2, fields, .. } => {
                    assert!(variant_index == *variant_index2);
                    &mut fields[field_index.index()]
                }
                _ => panic!("unexpected expr {:?}", expr),
            }
        }
        expr
    }
}

impl<'tcx> ReadExprExt<'tcx> for Operand<'tcx> {
    fn get_expr(&self, env: &mut Env<'tcx>, mir_access: MirAccess<'tcx>) -> Expr<'tcx> {
        match self {
            Operand::Copy(place) => place.get_expr(env, mir_access),
            Operand::Move(place) => {
                place.get_mut_expr(env, mir_access).replace(Expr::uninit(place.get_ty(mir_access)))
            }
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
        mir_access: MirAccess<'tcx>,
    ) -> Expr<'tcx>;
}

impl<'tcx> ReadExprCtxExt<'tcx> for Rvalue<'tcx> {
    type Context = (BasicBlock, usize);
    fn get_expr_at(
        &self,
        disambiguator: Self::Context,
        env: &mut Env<'tcx>,
        mir_access: MirAccess<'tcx>,
    ) -> Expr<'tcx> {
        let ty = self.get_ty(mir_access);
        match self {
            Rvalue::Use(opd) => opd.get_expr(env, mir_access),
            Rvalue::Ref(_, BorrowKind::Shared, place) => place.get_expr(env, mir_access),
            Rvalue::Ref(_, BorrowKind::Mut { .. }, referee) => {
                let body_ty = referee.get_ty(mir_access);
                referee.get_mut_expr(env, mir_access).do_borrow_mut(body_ty, ty, disambiguator)
            }
            Rvalue::BinaryOp(mir_bin_op, box (opd1, opd2)) => Expr::from_bin_op(
                BinOp::from_mir_bin_op(*mir_bin_op, opd1.get_ty(mir_access)),
                opd1.get_expr(env, mir_access),
                opd2.get_expr(env, mir_access),
            ),
            Rvalue::UnaryOp(mir_un_op, opd) => Expr::UnOp(
                UnOp::from_mir_un_op(*mir_un_op),
                Box::new(opd.get_expr(env, mir_access)),
            ),
            _ => panic!("unexpected rvalue {:?}", self),
        }
    }
}

pub fn set_tag<'tcx>(
    place: &Place<'tcx>,
    tag: VariantIdx,
    env: &mut Env<'tcx>,
    mir_access: MirAccess<'tcx>,
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
        _ => panic!("unexpected expr {:?}", expr),
    }
}

fn needs_drop<'tcx>(ty: Ty<'tcx>, mir_access: MirAccess<'tcx>) -> bool {
    fn needs_drop<'tcx>(ty: Ty<'tcx>, mir_access: MirAccess<'tcx>, seen: &mut Set<String>) -> bool {
        match &ty.kind() {
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => false,
            TyKind::Adt(adt_def, adt_substs) => {
                if let Some(ty) = adt_is_box(adt_def, adt_substs) {
                    needs_drop(ty, mir_access, seen)
                } else {
                    let key = rep(ty).to_string();
                    if seen.insert(key) {
                        adt_def.all_fields().any(|fld_def| {
                            needs_drop(
                                fld_def.get_ty_with(mir_access, adt_substs),
                                mir_access,
                                seen,
                            )
                        })
                    } else {
                        false
                    }
                }
            }
            TyKind::Ref(_, _, mutability) => matches!(mutability, Mutability::Mut),
            TyKind::Tuple(generic_args) => {
                generic_args.types().any(|ty| needs_drop(Ty::new(ty), mir_access, seen))
            }
            _ => panic!("unsupported type {}", ty),
        }
    }

    needs_drop(ty, mir_access, &mut Set::new())
}

pub trait DropExt<'tcx> {
    fn do_drop(&self, of_type: Ty<'tcx>, mir_access: MirAccess<'tcx>, conds: &mut Vec<Cond<'tcx>>);
}

impl<'tcx> DropExt<'tcx> for Path<'tcx> {
    fn do_drop(&self, ty: Ty<'tcx>, _: MirAccess<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
        fn drop_path<'tcx>(ty: Ty<'tcx>, path: &Path<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
            if let Path::Var(Var::Uninit, _) = path {
                return;
            }
            match &ty.kind() {
                TyKind::Ref(_, _, Mutability::Mut) => {
                    let (cur, ret) = Expr::decompose_mut_path(path);
                    conds.push(Cond::Eq { src: cur, tgt: ret });
                }
                TyKind::Adt(adt_def, adt_substs) => {
                    if let Some(ty) = adt_is_box(adt_def, adt_substs) {
                        drop_path(ty, path, conds);
                    } else {
                        conds.push(Cond::Drop { ty, arg: Expr::Path(path.clone()) });
                    }
                }
                _ => panic!("unexpected type {}", ty),
            }
        }

        drop_path(ty, self, conds);
    }
}

impl<'tcx> DropExt<'tcx> for Expr<'tcx> {
    fn do_drop(&self, ty: Ty<'tcx>, mir_access: MirAccess<'tcx>, conds: &mut Vec<Cond<'tcx>>) {
        match self {
            Expr::Path(path) => {
                if needs_drop(ty, mir_access) {
                    path.do_drop(ty, mir_access, conds);
                }
            }
            Expr::Aggregate { ty, variant_index, fields } => match &ty.kind() {
                TyKind::Ref(_, _, Mutability::Mut) => {
                    let (x, x_) = self.clone().decompose_mut();
                    conds.push(Cond::Eq { tgt: x_, src: x });
                }
                TyKind::Adt(adt_def, adt_substs) => {
                    assert!(!adt_def.is_box());
                    assert!(variant_index.index() < adt_def.variants.len());
                    let fld_defs = &adt_def.variants[*variant_index].fields;
                    assert!(fields.len() == fld_defs.len());
                    for (fld_def, fld) in fld_defs.iter().zip(fields) {
                        fld.do_drop(fld_def.get_ty_with(mir_access, adt_substs), mir_access, conds);
                    }
                }
                TyKind::Tuple(generic_args) => {
                    assert!(fields.len() == generic_args.types().count());
                    for (ty, fld) in generic_args.types().zip(fields) {
                        fld.do_drop(Ty::new(ty), mir_access, conds);
                    }
                }
                _ => panic!("unexpected type {} for aggregation", ty),
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
        mir_access: MirAccess<'tcx>,
    );
}

impl<'tcx> AssignExt<'tcx> for Place<'tcx> {
    fn assign(
        &self,
        new_expr: Expr<'tcx>,
        env: &mut Env<'tcx>,
        conds: &mut Vec<Cond<'tcx>>,
        mir_access: MirAccess<'tcx>,
    ) {
        let expr = self.get_mut_expr(env, mir_access);
        let old_expr = expr.replace(new_expr);
        old_expr.do_drop(self.get_ty(mir_access), mir_access, conds);
    }
}

#[derive(Debug)]
pub enum Cond<'tcx> {
    Drop { ty: Ty<'tcx>, arg: Expr<'tcx> },
    Eq { tgt: Expr<'tcx>, src: Expr<'tcx> },
    Neq { tgt: Expr<'tcx>, srcs: Vec<Expr<'tcx>> },
    Call { fun_ty: Ty<'tcx>, args: Vec<Expr<'tcx>> },
}
#[derive(Debug)]
pub enum End<'tcx> {
    Pivot { next_switch: BasicBlock, args: Vec<Expr<'tcx>> },
    Return { res: Option<Expr<'tcx>> },
    Panic,
    NeverReturn,
}

#[derive(Debug)]
/// Ask is a request to define at the beginning of the smt2 to be generated.
pub struct BasicAsks<'tcx> {
    pub fun_asks: Map<String, Ty<'tcx>>,
    pub drop_asks: Map<String, Ty<'tcx>>,
    pub adt_asks: Set<DefId>,
    pub tup_asks: Map<String, GenericArgsRef<'tcx>>,
    pub mut_asks: Map<String, Ty<'tcx>>,
}

pub trait GatherVars<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'tcx>,
        basic_asks: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    );
}

fn traverse_path<'tcx>(path: &Path<'tcx>, vars: &mut Map<Var, Ty<'tcx>>) {
    match path {
        Path::Var(var, ty) => {
            vars.insert(*var, *ty);
        }
        Path::Proj { body: box path, .. } => traverse_path(path, vars),
    }
}

impl<'tcx> GatherVars<'tcx> for Path<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'tcx>,
        _: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    ) {
        traverse_path(self, vars);
    }
}

impl<'tcx> GatherVars<'tcx> for Expr<'tcx> {
    fn gather_vars(
        &self,
        _: MirAccess<'tcx>,
        _: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    ) {
        fn traverse_expr<'tcx>(expr: &Expr<'tcx>, vars: &mut Map<Var, Ty<'tcx>>) {
            match expr {
                Expr::Path(path) => {
                    traverse_path(path, vars);
                }
                Expr::Const(_) => {}
                Expr::BinOp(_, box expr1, box expr2) => {
                    traverse_expr(expr1, vars);
                    traverse_expr(expr2, vars);
                }
                Expr::UnOp(_, box expr) => {
                    traverse_expr(expr, vars);
                }
                Expr::Aggregate { fields, .. } => {
                    for field in fields {
                        traverse_expr(field, vars);
                    }
                }
            }
        }

        traverse_expr(self, vars);
    }
}

impl<'tcx> GatherVars<'tcx> for Cond<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'tcx>,
        basic_asks: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    ) {
        match self {
            Cond::Drop { ty, arg } => {
                arg.gather_vars(mir_access, basic_asks, vars);
                let ty = *ty;
                basic_asks.drop_asks.insert(rep_drop_name(ty), ty);
            }
            Cond::Eq { tgt, src } => {
                tgt.gather_vars(mir_access, basic_asks, vars);
                src.gather_vars(mir_access, basic_asks, vars);
            }
            Cond::Neq { tgt, srcs } => {
                tgt.gather_vars(mir_access, basic_asks, vars);
                srcs.gather_vars(mir_access, basic_asks, vars);
            }
            Cond::Call { args, .. } => {
                args.gather_vars(mir_access, basic_asks, vars);
            }
        }
    }
}

impl<'tcx> GatherVars<'tcx> for End<'tcx> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'tcx>,
        basic_asks: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    ) {
        match self {
            End::Pivot { args, .. } => {
                args.gather_vars(mir_access, basic_asks, vars);
            }
            End::Return { res } => match res {
                Some(expr) => {
                    expr.gather_vars(mir_access, basic_asks, vars);
                }
                None => {}
            },
            End::Panic | End::NeverReturn => {}
        };
    }
}

impl<'tcx, T: GatherVars<'tcx>> GatherVars<'tcx> for Vec<T> {
    fn gather_vars(
        &self,
        mir_access: MirAccess<'tcx>,
        basic_asks: &mut BasicAsks<'tcx>,
        vars: &mut Map<Var, Ty<'tcx>>,
    ) {
        for item in self {
            item.gather_vars(mir_access, basic_asks, vars);
        }
    }
}

impl<'tcx> BasicAsks<'tcx> {
    fn update_by_ty(&mut self, ty: Ty<'tcx>, mir_access: MirAccess<'tcx>) {
        match &ty.kind() {
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {}
            TyKind::Adt(adt_def, adt_substs) => {
                if adt_def.is_box() {
                    for ty in adt_substs.types() {
                        self.update_by_ty(Ty::new(ty), mir_access);
                    }
                } else if self.adt_asks.insert(adt_def.did) {
                    for fld_def in adt_def.all_fields() {
                        self.update_by_ty(fld_def.get_ty_with(mir_access, adt_substs), mir_access);
                    }
                }
            }
            TyKind::Ref(_, ty, mutability) => {
                let ty = Ty::new(ty);
                if let Mutability::Mut = mutability {
                    self.mut_asks.insert(rep(ty).to_string(), ty);
                }
                self.update_by_ty(ty, mir_access);
            }
            TyKind::Tuple(generic_args) => {
                self.tup_asks.insert(rep(generic_args).to_string(), generic_args);
                for ty in generic_args.types() {
                    let ty = Ty::new(ty);
                    self.update_by_ty(ty, mir_access);
                }
            }
            _ => panic!("unsupported type {}", ty),
        }
    }

    pub fn update_by_vars(
        &mut self,
        vars: Map<Var, Ty<'tcx>>,
        mir_access: MirAccess<'tcx>,
    ) -> Vec<(Var, Ty<'tcx>)> {
        let vars = vars.into_sorted_vec();
        for (_, ty) in &vars {
            self.update_by_ty(*ty, mir_access);
        }
        vars
    }
}
