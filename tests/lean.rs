use egg::{rewrite as rw, *};

define_language! {
    pub enum Expr {
        Nat(u64),
        String(Symbol),
        "bvar"    = BVar(Id),
        "fvar"    = FVar(Id),
        "mvar"    = MVar(Id),
        "sort"    = Sort(Id),
        "const"   = Const(Id), // ignore universe levels
        "app"     = App([Id; 2]),
        "lam"     = Lam([Id; 3]), // ignore binderInfo 
        "forallE" = ForallE([Id; 3]), // ignore binderInfo
        "letE"    = LetE([Id; 4]), // ignore declName and nonDep 
        "lit"     = Lit(Id),
        "proj"    = Proj([Id; 3]), 
    }
}

pub fn rules() -> Vec<Rewrite<Expr, ()>> { vec![
    rw! { 
        "beta"; 
        "(app (lam ?x ?t ?b) ?y)" => "(letE ?x ?t ?y ?b)" },
    rw! {
        "zeta-exact";
        "(letE ?x ?t ?y ?x)" => "?y" },
    rw! {
        "eta"; 
        "(lam ?x ?t (app ?f ?x))" => "?f" },
]}

egg::test_fn! {
    beta_reduction_1, rules(),
    "(app (lam x (const Nat) x) y)" => "y"
}
