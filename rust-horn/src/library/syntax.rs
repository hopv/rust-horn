#[derive(Debug, Clone)]
pub struct Ident(String);

#[derive(Debug, Clone)]
pub struct Block {
    // pub brace_token: Brace,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Local(Local),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct Local {
    pub pat: Pat,
    pub init: Option<LocalInit>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Ident(Ident),
    Tuple(PatTuple),
}

#[derive(Debug, Clone)]
pub struct PatTuple {
    // pub paren_token: Paren,
    pub elems: Vec<Pat>,
}

#[derive(Debug, Clone)]
pub struct LocalInit {
    // pub eq_token: Eq,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum Expr {}
