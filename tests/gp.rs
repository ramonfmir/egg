use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;

define_language! {
    pub enum Optimization {
        "prob" = Prob([Id; 2]),
        "objFun" = ObjFun(Id),
        "constraints" = Constraints(Id),

        "and" = And([Id; 2]),
        "eq" = Eq([Id; 2]),
        "le" = Le([Id; 2]),

        "neg" = Neg(Id),
        "add" = Add([Id; 2]),
        "mul" = Mul([Id; 2]),
        "pow" = Pow([Id; 2]),
        "log" = Log(Id),
        "exp" = Exp(Id),
        
        "var" = Var(Id),

        Symbol(Symbol),
        Float(u64),
    }
}

type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta;

#[derive(Debug)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let before_len = to.free_vars.len();
        to.free_vars.extend(&from.free_vars);
        DidMerge(
            before_len != to.free_vars.len(),
            to.free_vars.len() != from.free_vars.len(),
        )
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_vars = 
            |i: &Id| egraph[*i].data.free_vars.iter().cloned();
        
        let mut free_vars = HashSet::default();
        
        println!("enode: {:?}", enode);

        match enode {
            Optimization::Prob([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::ObjFun(a) => {
                free_vars.extend(get_vars(a));
            }
            Optimization::Constraints(a) => {
                free_vars.extend(get_vars(a));
            }
            Optimization::And([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Eq([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Le([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Neg(a) => {
                free_vars.extend(get_vars(a))
            }
            Optimization::Add([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Mul([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Pow([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Log(a) => {
                free_vars.extend(get_vars(a))
            }
            Optimization::Exp(a) => {
                free_vars.extend(get_vars(a))
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        free_vars.insert((*a, s)); 
                    }
                    _ => {}
                }
            }
            Optimization::Symbol(_) => {}
            Optimization::Float(_) => {}
        }

        println!("final vars: {:?}", free_vars);

        Data { free_vars }
    }
}

#[derive(Default)]
struct MapExp {
}

impl Applier<Optimization, Meta> for MapExp {
    fn apply_one(
        &self, 
        egraph: &mut EGraph, 
        matched_id: Id, 
        subst: &Subst, 
        searcher_pattern: Option<&PatternAst<Optimization>>, 
        rule_name: Symbol
    ) -> Vec<Id> {
        let free_vars : HashSet<(Id, Symbol)> = egraph[matched_id].data.free_vars.clone();

        let mut res = vec![];

        for (id, sym) in free_vars {
            let n = egraph.add(Optimization::Symbol(format!("_{}", sym).into()));
            let var = egraph.add(Optimization::Var(n));
            let exp = egraph.add(Optimization::Exp(var));
            // if egraph.union(id, exp) {
            //     res.push(id);
            //     println!("exp var: {:?}", exp);
            // }
        }

        return res; 
    }
}

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("and-comm"; 
        "(and ?a ?b)" => "(and ?b ?a)"),

    rw!("map-domain-exp"; 
        "(prob (objFun ?o) (constraints ?cs))" => { MapExp {} } )
]}

egg::test_fn! {
    test_1, rules(),
    "(prob 
        (objFun (var x)) 
        (constraints 
            (le 1.0 (var x))
        )
    )" => 
    "(prob 
        (objFun (exp (var _x))) 
        (constraints 
            (le 1.0 (exp (var _x)))
        )
    )"
}
