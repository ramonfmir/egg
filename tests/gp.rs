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
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
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
        //to.free_vars.extend(&from.free_vars);
        to.free_vars.retain(|i| from.free_vars.contains(i));
        DidMerge(
            before_len != to.free_vars.len(),
            to.free_vars.len() != from.free_vars.len(),
        )
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_vars = 
            |i: &Id| egraph[*i].data.free_vars.iter().cloned();
        
        let mut free_vars = HashSet::default();

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
            Optimization::Sub([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Mul([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Div([a, b]) => {
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

        Data { free_vars }
    }

    fn modify(egraph: &mut egg::EGraph<Optimization, Self>, id: Id) {
        // Do nothing.
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
        //print!("EGraph {:?}", egraph.dump());
        let free_vars : HashSet<(Id, Symbol)> = egraph[matched_id].data.free_vars.clone();

        let mut res = vec![];

        for (id, sym) in free_vars {
            let y = egraph.add(Optimization::Symbol(sym));
            let var = egraph.add(Optimization::Var(y));
            let exp = egraph.add(Optimization::Exp(var));
            
            if let Some((_, parent_id)) = egraph[id].parents().last() {
                if egraph.union(parent_id, exp) {
                    res.push(parent_id);
                }
            }
        }
        
        return res; 
    }
}

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
    rw!("and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
    
    rw!("eq-symm"; "(eq ?a ?b)" => "(eq ?b ?a)"),
    
    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    rw!("add-0-right"; "(add ?a 0.0)" => "?a"),
    rw!("add-0-left"; "(add 0.0 ?a)" => "?a"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),
    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),
    rw!("mul-1-right"; "(mul ?a 1.0)" => "?a"),
    rw!("mul-1-left"; "(mul 1.0 ?a)" => "?a"),
    rw!("mul-0-right"; "(mul ?a 0.0)" => "0.0"),
    rw!("mul-0-left"; "(mul 0.0 ?a)" => "0.0"),

    rw!("sub-0"; "(sub ?a 0.0)" => "?a"),

    rw!("pow-1"; "(pow ?a 1.0)" => "?a"),
    rw!("pow-0"; "(pow ?a 0.0)" => "1.0"),

    rw!("log-1"; "(log 1.0)" => "0.0"),

    rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),
    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))"),

    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))"),
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
        (objFun (exp (var x))) 
        (constraints 
            (le 1.0 (exp (var x)))
        )
    )"
}

egg::test_fn! {
    test_2, rules(),
    "(prob 
        (objFun (mul (var x) (var y))) 
        (constraints 
            (le 1.0 (mul (var x) (var y)))
        )
    )" => 
    "(prob 
        (objFun (add (var x) (var y))) 
        (constraints 
            (le 0.0 (add (var x) (var y)))
        )
    )"
}

egg::test_fn! {
    test_3, rules(),
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints 
            (and 
                (le 2.0 (var x))
                (and 
                    (le (var x) 3.0) 
                    (and 
                        (le (add (pow (var x) 2.0) (mul 3.0 (div (var y) (var z)))) (pow (var y) 0.5)) 
                        (eq (mul (var x) (var y)) (var z))))
            )
        )
    )" => 
    "(prob 
        (objFun (add (var x) (var y))) 
        (constraints 
            (le 0.0 (add (var x) (var y)))
        )
    )"
}

// #[derive(Debug)]
// pub struct AntiAstSize;
// impl<L: Language> CostFunction<L> for AntiAstSize {
//     type Cost = i32;
//     fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
//     where
//         C: FnMut(Id) -> Self::Cost,
//     {
//         0
//     }
// }

// fn simplify(s: &str) -> String {
//     let expr: RecExpr<Optimization> = s.parse().unwrap();

//     let runner = Runner::default().with_expr(&expr).run(&rules());
    
//     let root = runner.roots[0];

//     let extractor = Extractor::new(&runner.egraph, AntiAstSize);
//     let (best_cost, best) = extractor.find_best(root);
//     println!("Simplified {} to {} with cost {}", expr, best, best_cost);

//     //print!("{}", runner.egraph);

//     return best.to_string();
// }


// #[test]
// fn simple_tests() {
//     let r = simplify("
//     (prob 
//         (objFun (var x)) 
//         (constraints 
//             (le 1.0 (var x))
//         )
//     )");
//     println!("simplified: {}", r);
// }
