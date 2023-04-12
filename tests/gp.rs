use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use instant::Duration;
use ordered_float::NotNan;

pub type Constant = NotNan<f64>;

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

        Constant(Constant),
        Symbol(Symbol),
    }
}

type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta;

#[derive(Debug, Clone)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
    constant: Option<Constant>,
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
        let get_constant = 
            |i: &Id| egraph[*i].data.constant.clone();
        
        let mut free_vars = HashSet::default();
        let mut constant: Option<Constant> = None;

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
                free_vars.extend(get_vars(a));
                match get_constant(a) {
                    Some(c) => { 
                        constant = Some(-c); 
                    }
                    _ => {}
                }
            }
            Optimization::Add([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some(c1), Some(c2)) => { 
                        constant = Some(c1 + c2); 
                    }
                    _ => {}
                }
            }
            Optimization::Sub([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some(c1), Some(c2)) => { 
                        constant = Some(c1 - c2); 
                    }
                    _ => {}
                }
            }
            Optimization::Mul([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some(c1), Some(c2)) => { 
                        constant = Some(c1 * c2); 
                    }
                    _ => {}
                }
            }
            Optimization::Div([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some(c1), Some(c2)) => { 
                        constant = Some(c1 / c2); 
                    }
                    _ => {}
                }
            }
            Optimization::Pow([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some(c1), Some(c2)) => { 
                        constant = Some(NotNan::new(c1.powf(c2.into())).unwrap()); 
                    }
                    _ => {}
                }
            }
            Optimization::Log(a) => {
                free_vars.extend(get_vars(a));
                match get_constant(a) {
                    Some(c) => { 
                        constant = Some(NotNan::new(c.ln()).unwrap()); 
                    }
                    _ => {}
                }
            }
            Optimization::Exp(a) => {
                free_vars.extend(get_vars(a));
                match get_constant(a) {
                    Some(c) => { 
                        constant = Some(NotNan::new(c.exp()).unwrap()); 
                    }
                    _ => {}
                }
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
            Optimization::Constant(f) => {
                constant = Some(*f);
            }
        }

        Data { free_vars, constant }
    }

    fn modify(egraph: &mut egg::EGraph<Optimization, Self>, id: Id) {
        // Constant fold.
        let constant = egraph[id].data.constant.clone();
        if let Some(c) = constant {
            let const_id = egraph.add(Optimization::Constant(c));
            egraph.union(id, const_id);

            // To not prune, comment this out.
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
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
        _subst: &Subst, 
        _searcher_pattern: Option<&PatternAst<Optimization>>, 
        _rule_name: Symbol
    ) -> Vec<Id> {
        //print!("EGraph {:?}", egraph.dump());
        let free_vars : HashSet<(Id, Symbol)> = egraph[matched_id].data.free_vars.clone();

        let mut res = vec![];

        for (id, sym) in free_vars {            
            if let Some((_, parent_id)) = egraph[id].parents().last() {
                if egraph[parent_id].nodes.len() > 1 {
                    continue;
                }

                let y = egraph.add(Optimization::Symbol(sym));
                let var = egraph.add(Optimization::Var(y));
                let exp = egraph.add(Optimization::Exp(var));

                // We make (var x) = (exp (var x)).
                if egraph.union(parent_id, exp) {
                    res.push(parent_id);
                }
            }
        }
        
        return res; 
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data.constant {
            *(n) != 0.0
        } else {
            true
        }
    }
}

fn is_gt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data.constant {
            (*n).into_inner() > 0.0
        } else {
            true
        }
    }
}

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
    rw!("and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
    
    rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),
    rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),
    rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" if is_not_zero("c")),
    rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)"),

    rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"),
    rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" if is_not_zero("b")),

    rw!("le-sub"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),
    rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),
    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" if is_not_zero("c")),
    rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)"),

    rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)"),
    rw!("le-div-one"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" if is_not_zero("b")),

    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    rw!("add-0-right"; "(add ?a 0)" => "?a"),
    rw!("add-0-left"; "(add 0 ?a)" => "?a"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),
    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),
    rw!("mul-1-right"; "(mul ?a 1)" => "?a"),
    rw!("mul-1-left"; "(mul 1 ?a)" => "?a"),
    //rw!("mul-1-left-gen"; "?a" => "(mul 1 ?a)"),
    rw!("mul-0-right"; "(mul ?a 0)" => "0"),
    rw!("mul-0-left"; "(mul 0 ?a)" => "0"),

    rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),
    rw!("sub-add"; "(sub (add ?a ?b) ?c)" => "(add ?a (sub ?b ?c))"),

    rw!("mul-add"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),
    rw!("add-mul"; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))"),

    rw!("add-mul-same"; "(add ?a (mul ?b ?a))" => "(mul ?a (add 1 ?b))"),

    rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),
    rw!("sub-mul-left"; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))"),
    rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => "(mul (sub ?a ?c) ?b)"),

    rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),
    rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    rw!("mul-div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"),
    rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),

    rw!("div-1"; "(div ?a 1.0)" => "?a"),

    rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))"),
    rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))"),
    rw!("sub-div"; "(sub (div ?a ?b) (div ?c ?b))" => "(div (sub ?a ?c) ?b)"),

    rw!("sub-0"; "(sub ?a 0)" => "?a"),

    rw!("pow-1"; "(pow ?a 1)" => "?a"),
    rw!("pow-0"; "(pow ?a 0)" => "1"),

    rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),
    rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" if is_not_zero("?a")),
    rw!("div-pow"; "(div (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (sub ?b ?c))"),

    rw!("exp-0"; "(exp 0)" => "1"),

    rw!("log-1"; "(log 1)" => "0"),

    rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),
    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),
    rw!("div-exp"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),

    rw!("pow-exp"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    rw!("log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))"),
    rw!("log-div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))"),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    rw!("eq-log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b")),
    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))" if is_gt_zero("?a")),
    rw!("map-domain-exp"; 
        "(prob (objFun ?o) (constraints ?cs))" => { MapExp {} } )
]}

egg::test_fn! {
    test_exp_map, rules(),
    "(prob 
        (objFun (var x)) 
        (constraints 
            (le 1 (var x))
        )
    )" => 
    "(prob 
        (objFun (exp (var x))) 
        (constraints 
            (le 1 (exp (var x)))
        )
    )"
}

egg::test_fn! {
    test_exp_log_mul_le_mul, rules(),
    "(prob 
        (objFun (mul (var x) (var y))) 
        (constraints 
            (le 1 (mul (var x) (var y)))
        )
    )" => 
    "(prob 
        (objFun (add (var x) (var y))) 
        (constraints 
            (le 0 (add (var x) (var y)))
        )
    )"
}

egg::test_fn! {
    test_exp_log_div_le, rules(), 
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints 
            (le 2 (var x))
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (le (log 2) (var x))
        )
    )"
}

egg::test_fn! {
    test_exp_log_div_eq_mul, rules(), 
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints 
            (eq (mul (var x) (var y)) (var z))
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (eq (sub (add (var x) (var y)) (var z)) 0)
        )
    )"
}

egg::test_fn! {
    test_exp_log_div_and_le_eq_mul, rules(), 
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints
            (and 
                (le 2 (var x))
                (eq (mul (var x) (var y)) (var z))
            )
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (and
                (eq (sub (add (var x) (var y)) (var z)) 0)
                (le (log 2) (var x))
            )
        )
    )"
}

egg::test_fn! {
    test_exp_log_le_pow, rules(), 
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints
            (le (pow (var x) 2) (pow (var y) 0.5))
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (le (mul 2 (var x)) (mul 0.5 (var y)))
        )
    )"
}

egg::test_fn! {
    test_exp_log_le_mul_div, rules(), 
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints
            (le (mul 3 (div (var y) (var z))) 1)
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (le (mul 3 (exp (sub (var y) (var z)))) 1)
        )
    )"
}

egg::test_fn! {
    test_constant_fold, rules(), 
    "(sub 3 1)" => 
    "2"
}

egg::test_fn! {
    test_le_mul_constant_fold, rules(), 
    "(le (mul 3 (var x)) (var x))" => 
    "(le (mul 2 (var x)) 0)"
}

egg::test_fn! {
    test_le_pow_div_through, rules(), 
    "(le (pow (var x) 0.5) (var x))" => 
    "(le (pow (var x) (-0.5)) 1)"
}

//(le (add (pow (var x) 2.0) (mul 3.0 (div (var y) (var z)))) (pow (var y) 0.5)) 

// (le 
//     (add 
//         (exp (sub (mul 2.0 (var x)) (mul 0.5 (var y)))) 
//         (mul 3.0 (exp (sub (mul 0.5 (var y)) (var z))))
//     ) 
//     1.0
// ) 

egg::test_fn! {
    test_3, rules(), 
    runner = 
        Runner::default()
        .with_node_limit(1000000)
        .with_iter_limit(100)
        .with_time_limit(Duration::from_secs(100)),
    "(prob 
        (objFun (div (var x) (var y))) 
        (constraints 
            (and 
                (le 2 (var x))
                (and 
                    (le (var x) 3) 
                    (and 
                        (le (add (pow (var x) 2.0) (mul 3.0 (div (var y) (var z)))) (pow (var y) 0.5)) 
                        (eq (mul (var x) (var y)) (var z))
                    )
                
                )
            )
        )
    )" => 
    "(prob 
        (objFun (sub (var x) (var y))) 
        (constraints 
            (and 
                (le (log 2.0) (var x))
                (and 
                    (le (var x) (log 3.0)) 
                    (and 
                        (le 
                            (add 
                                (exp (sub (mul 2.0 (var x)) (mul 0.5 (var y)))) 
                                (mul 3.0 (exp (sub (mul 0.5 (var y)) (var z))))
                            ) 
                            1.0
                        ) 
                        (eq (sub (add (var x) (var y)) (var z)) 0.0)))
            )
        )
    )"
}

egg::test_fn! {
    test_5, rules(), 
    runner = 
        Runner::default()
        .with_node_limit(1000000)
        .with_iter_limit(10000)
        .with_time_limit(Duration::from_secs(30)),
    "(le 
        (add 
            (pow (exp (var x)) 2.0) 
            (mul 3.0 (div (exp (var y)) (exp (var z))))
        ) 
        (pow (exp (var y)) 0.5)
    )" => 
    "(le 
        (add 
            (exp (sub (mul 2.0 (var x)) (mul 0.5 (var y)))) 
            (mul 3.0 (exp (sub (mul 0.5 (var y)) (var z))))
        ) 
        1.0
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
