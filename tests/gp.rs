use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;
use instant::Duration;
use ordered_float::NotNan;
use std::fs;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Curvature {
    Convex,
    Concave,
    Affine,
    Constant,
    Valid,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
    constant: Option<(Constant, PatternAst<Optimization>)>,
    curvature: Curvature,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let before_len = to.free_vars.len();

        println!("Merging {:?} {:?}", from.curvature, to.curvature);

        // if from.curvature == Curvature::Affine {
        //     to.curvature = Curvature::Affine;
        // }

        // if to.curvature == Curvature::Unknown {
        //     to.curvature = from.curvature.clone();
        // }

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
        let get_curvature = 
            |i: &Id| egraph[*i].data.curvature.clone();
        
        let mut free_vars = HashSet::default();
        let mut constant: Option<(Constant, PatternAst<Optimization>)> = None;
        let mut curvature = Curvature::Unknown;

        match enode {
            Optimization::Prob([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                // if get_curvature(a) == Curvature::Convex && get_curvature(b) == Curvature::Valid {
                //     curvature = Curvature::Convex;
                // }
            }
            Optimization::ObjFun(a) => {
                free_vars.extend(get_vars(a));
                // if get_curvature(a) == Curvature::Convex || get_curvature(a) == Curvature::Affine  {
                //     curvature = Curvature::Convex;
                // }
            }
            Optimization::Constraints(a) => {
                free_vars.extend(get_vars(a));
                curvature = get_curvature(a);
            }
            Optimization::And([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                // if get_curvature(a) == Curvature::Valid && get_curvature(b) == Curvature::Valid {
                //     curvature = Curvature::Valid;
                // }
            }
            Optimization::Eq([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                // if get_curvature(a) == Curvature::Affine && get_curvature(b) == Curvature::Affine {
                //     curvature = Curvature::Valid;
                // }
            }
            Optimization::Le([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                // match (get_curvature(a), get_curvature(b)) {
                //     (Curvature::Convex,   Curvature::Concave)  => { curvature = Curvature::Valid; }
                //     (Curvature::Convex,   Curvature::Affine)   => { curvature = Curvature::Valid; }
                //     (Curvature::Convex,   Curvature::Constant) => { curvature = Curvature::Valid; }
                //     (Curvature::Affine,   Curvature::Concave)  => { curvature = Curvature::Valid; }
                //     (Curvature::Constant, Curvature::Concave)  => { curvature = Curvature::Valid; }
                //     (Curvature::Affine,   Curvature::Affine)   => { curvature = Curvature::Valid; }
                //     (Curvature::Constant, Curvature::Affine)   => { curvature = Curvature::Valid; }
                //     (Curvature::Affine,   Curvature::Constant) => { curvature = Curvature::Valid; }
                //     (Curvature::Constant, Curvature::Constant) => { curvature = Curvature::Valid; }
                //     _ => { curvature = Curvature::Unknown; }
                // } 
            }
            Optimization::Neg(a) => {
                free_vars.extend(get_vars(a));
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((-c, format!("(neg {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                // if get_curvature(a) == Curvature::Convex {
                //     curvature = Curvature::Concave;
                // } else if get_curvature(a) == Curvature::Concave {
                //     curvature = Curvature::Convex;
                // } else if get_curvature(a) == Curvature::Affine {
                //     curvature = Curvature::Affine;
                // } else if get_curvature(a) == Curvature::Constant {
                //     curvature = Curvature::Constant;
                // }
            }
            Optimization::Add([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((c1 + c2, format!("(add {} {})", c1, c2).parse().unwrap())); 
                        // curvature = Curvature::Constant;
                    }
                    _ => {}
                }
                // match (get_curvature(a), get_curvature(b)) {
                //     (Curvature::Convex,   Curvature::Convex)   => { curvature = Curvature::Convex; }
                //     (Curvature::Convex,   Curvature::Affine)   => { curvature = Curvature::Convex; }
                //     (Curvature::Convex,   Curvature::Constant) => { curvature = Curvature::Convex; }
                //     (Curvature::Affine,   Curvature::Convex)   => { curvature = Curvature::Convex; }
                //     (Curvature::Constant, Curvature::Convex)   => { curvature = Curvature::Convex; }

                //     (Curvature::Concave,  Curvature::Concave)  => { curvature = Curvature::Concave; }
                //     (Curvature::Concave,  Curvature::Affine)   => { curvature = Curvature::Concave; }
                //     (Curvature::Concave,  Curvature::Constant) => { curvature = Curvature::Concave; }
                //     (Curvature::Affine,   Curvature::Concave)  => { curvature = Curvature::Concave; }
                //     (Curvature::Constant, Curvature::Concave)  => { curvature = Curvature::Concave; }

                //     (Curvature::Affine,   Curvature::Affine)   => { curvature = Curvature::Affine; }
                //     (Curvature::Affine,   Curvature::Constant) => { curvature = Curvature::Affine; }
                //     (Curvature::Constant, Curvature::Affine)   => { curvature = Curvature::Affine; }

                //     (Curvature::Constant, Curvature::Constant) => { curvature = Curvature::Constant; }
                //     _ => {}
                // }
            }
            Optimization::Sub([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((c1 - c2, format!("(sub {} {})", c1, c2).parse().unwrap())); 
                        // curvature = Curvature::Constant;
                    }
                    _ => {}
                }
                // match (get_curvature(a), get_curvature(b)) {
                //     (Curvature::Convex,   Curvature::Concave)  => { curvature = Curvature::Convex; }
                //     (Curvature::Convex,   Curvature::Affine)   => { curvature = Curvature::Convex; }
                //     (Curvature::Convex,   Curvature::Constant) => { curvature = Curvature::Convex; }
                //     (Curvature::Affine,   Curvature::Concave)  => { curvature = Curvature::Convex; }
                //     (Curvature::Constant, Curvature::Concave)  => { curvature = Curvature::Convex; }

                //     (Curvature::Concave,  Curvature::Convex)   => { curvature = Curvature::Concave; }
                //     (Curvature::Concave,  Curvature::Affine)   => { curvature = Curvature::Concave; }
                //     (Curvature::Concave,  Curvature::Constant) => { curvature = Curvature::Concave; }
                //     (Curvature::Affine,   Curvature::Convex)   => { curvature = Curvature::Concave; }
                //     (Curvature::Constant, Curvature::Convex)   => { curvature = Curvature::Concave; }

                //     (Curvature::Affine,   Curvature::Affine)   => { curvature = Curvature::Affine; }
                //     (Curvature::Affine,   Curvature::Constant) => { curvature = Curvature::Affine; }
                //     (Curvature::Constant, Curvature::Affine)   => { curvature = Curvature::Affine; }

                //     (Curvature::Constant, Curvature::Constant) => { curvature = Curvature::Constant; }
                //     _ => {}
                // }
            }
            Optimization::Mul([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((c1 * c2, format!("(mul {} {})", c1, c2).parse().unwrap())); 
                        // curvature = Curvature::Constant;
                    }
                    // (Some((c1, _)), None) => {
                    //     if c1.into_inner() < 0.0 {
                    //         if get_curvature(b) == Curvature::Concave {
                    //             curvature = Curvature::Convex;
                    //         } else if get_curvature(b) == Curvature::Convex {
                    //             curvature = Curvature::Concave;
                    //         } else if get_curvature(b) == Curvature::Affine {
                    //             curvature = Curvature::Affine;
                    //         }
                    //     } else if c1.into_inner() > 0.0 {
                    //         if get_curvature(b) == Curvature::Concave {
                    //             curvature = Curvature::Concave;
                    //         } else if get_curvature(b) == Curvature::Convex {
                    //             curvature = Curvature::Convex;
                    //         } else if get_curvature(b) == Curvature::Affine {
                    //             curvature = Curvature::Affine;
                    //         }
                    //     } else {
                    //         curvature = Curvature::Constant;
                    //     }
                    // }
                    // (None, Some((c2, _))) => {
                    //     if c2.into_inner() < 0.0 {
                    //         if get_curvature(a) == Curvature::Concave {
                    //             curvature = Curvature::Convex;
                    //         } else if get_curvature(a) == Curvature::Convex {
                    //             curvature = Curvature::Concave;
                    //         } else if get_curvature(a) == Curvature::Affine {
                    //             curvature = Curvature::Affine;
                    //         }
                    //     } else if c2.into_inner() > 0.0 {
                    //         if get_curvature(a) == Curvature::Concave {
                    //             curvature = Curvature::Concave;
                    //         } else if get_curvature(a) == Curvature::Convex {
                    //             curvature = Curvature::Convex;
                    //         } else if get_curvature(a) == Curvature::Affine {
                    //             curvature = Curvature::Affine;
                    //         }
                    //     } else {
                    //         curvature = Curvature::Constant;
                    //     }
                    // }
                    _ => {}
                }
            }
            Optimization::Div([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((c1 / c2, format!("(div {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }

            }
            Optimization::Pow([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Log(a) => {
                free_vars.extend(get_vars(a));
                // if get_curvature(a) == Curvature::Affine || get_curvature(a) == Curvature::Concave {
                //     curvature = Curvature::Concave;
                // }
                // if get_curvature(a) == Curvature::Constant {
                //     curvature = Curvature::Constant;
                // }
            }
            Optimization::Exp(a) => {
                free_vars.extend(get_vars(a));
                // if get_curvature(a) == Curvature::Affine || get_curvature(a) == Curvature::Convex {
                //     curvature = Curvature::Convex;
                // }
                // if get_curvature(a) == Curvature::Constant {
                //     curvature = Curvature::Constant;
                // }
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        free_vars.insert((*a, s)); 
                    }
                    _ => {}
                }
                // curvature = Curvature::Affine;
            }
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                constant = Some((*f, format!("{}", f).parse().unwrap()));
                // curvature = Curvature::Constant;
            }
        }

        Data { free_vars, constant, curvature }
    }

    fn modify(egraph: &mut egg::EGraph<Optimization, Self>, id: Id) {
        // Constant fold.
        let constant = egraph[id].data.constant.clone();
        if let Some((c, pat)) = constant {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant-fold".to_string(),
                );
            } 
            else {
                let const_id = egraph.add(Optimization::Constant(c));
                egraph.union(id, const_id);
            }

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

                // We make (var x) = (exp (var x)).
                if egraph.are_explanations_enabled() {
                    let (new_id, did_union) = egraph.union_instantiations(
                        &format!("(var {})", sym).parse().unwrap(),
                        &format!("(exp (var {}))", sym).parse().unwrap(),
                        &Default::default(),
                        "map-exp".to_string(),
                    );
                    if did_union {
                        res.push(parent_id);
                    }
                }
                else {
                    let y = egraph.add(Optimization::Symbol(sym));
                    let var = egraph.add(Optimization::Var(y));
                    let exp = egraph.add(Optimization::Exp(var));

                    // egraph[parent_id].data.curvature = Curvature::ExpVar;
                    if egraph.union(parent_id, exp) {
                        res.push(parent_id);
                    }
                }
            }
        }
        
        return res; 
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            *(n) != 0.0
        } else {
            true
        }
    }
}

fn is_gt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            (*n).into_inner() > 0.0
        } else {
            true
        }
    }
}

// fn log_le_curv_check(a: &str, b: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
//     let a = a.parse().unwrap();
//     let b = b.parse().unwrap();
//     move |egraph, _, subst| {
//         let curv_a = &egraph[subst[a]].data.curvature;
//         let curv_b = &egraph[subst[b]].data.curvature;
//         if *curv_b == Curvature::Convex {
//             true 
//         } else {
//             false
//         }
//     }
// }

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    // rw!("and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
    // rw!("and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
    
    // rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),
    // rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),
    // rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" if is_not_zero("?c")),
    // rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)" if is_not_zero("?c")),

    // rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"),
    // rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" if is_not_zero("?b")),

    // rw!("le-sub"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),
    // rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),
    // rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" if is_not_zero("?c")),
    // rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)" if is_not_zero("?c")),

    // rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)"),
    // rw!("le-div-one"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" if is_not_zero("?b")),

    // rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
    // rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    // rw!("add-0-right"; "(add ?a 0)" => "?a"),
    // rw!("add-0-left"; "(add 0 ?a)" => "?a"),
    
    // rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),
    // rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),
    // rw!("mul-1-right"; "(mul ?a 1)" => "?a"),
    // rw!("mul-1-left"; "(mul 1 ?a)" => "?a"),
    // rw!("mul-0-right"; "(mul ?a 0)" => "0"),
    // rw!("mul-0-left"; "(mul 0 ?a)" => "0"),

    // rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),
    // rw!("sub-add"; "(sub (add ?a ?b) ?c)" => "(add ?a (sub ?b ?c))"),

    // rw!("mul-add"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),
    // rw!("add-mul"; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))"),

    // rw!("add-mul-same"; "(add ?a (mul ?b ?a))" => "(mul ?a (add 1 ?b))"),

    // rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),
    // rw!("sub-mul-left"; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))"),
    // rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => "(mul (sub ?a ?c) ?b)"),

    // rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),
    // rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    // rw!("mul-div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)" if is_not_zero("?c")),
    // rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),

    // rw!("div-1"; "(div ?a 1.0)" => "?a"),
    
    // rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" if is_not_zero("?c")),
    // rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    // rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" if is_not_zero("?c")),
    // rw!("sub-div"; "(sub (div ?a ?b) (div ?c ?b))" => "(div (sub ?a ?c) ?b)"),

    // rw!("sub-0"; "(sub ?a 0)" => "?a"),

    // rw!("pow-1"; "(pow ?a 1)" => "?a"),
    // rw!("pow-0"; "(pow ?a 0)" => "1"),

    // rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),
    // rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    // rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" if is_not_zero("?a")),
    // rw!("div-pow"; "(div (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (sub ?b ?c))"),

    // rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),
    // rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    // rw!("exp-0"; "(exp 0)" => "1"),

    // rw!("log-1"; "(log 1)" => "0"),

    // rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),
    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    // rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),
    // rw!("div-exp"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),

    // rw!("pow-exp"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    // rw!("log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b")),
    // rw!("log-div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    // rw!("eq-log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b")),
    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" if is_gt_zero("?a") if is_gt_zero("?b") if log_le_curv_check("?a", "?b")),

    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))" if is_gt_zero("?a")),
    rw!("map-domain-exp"; 
        "(prob (objFun ?o) (constraints ?cs))" => { MapExp {} } )
]}

// Test exp map.
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

// Test as above with log map and le constraint with multiplication.
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

// Test as above objective function with division.
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

// Test as above with an equality constraint.
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

// Test combining the two previous tests with an and.
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

// Test including powers.
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

// Test with mul and div on the constraint.
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

// Test constant fold.
egg::test_fn! {
    test_constant_fold, rules(), 
    "(sub 3 1)" => 
    "2"
}

// Test constant fold on le.
egg::test_fn! {
    test_le_mul_constant_fold, rules(), 
    "(le (mul 3 (var x)) (var x))" => 
    "(le (mul 2 (var x)) 0)"
}

// Test diving through a power.
egg::test_fn! {
    test_le_pow_div_through, rules(), 
    "(le (pow (var x) 0.5) (var x))" => 
    "(le (pow (var x) (-0.5)) 1)"
}

// Test from e1 to e2:
//     e1 : (e^x)^2 + 3(e^y)/(e^z) <= (e^y)^0.5  
//     e2 : e^(2x - 0.5y) + 3e^(0.5y - z) <= 1
egg::test_fn! {
    test_exp_log_le_pow_div_through_hard, rules(), 
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

// Test full geometric program.
egg::test_fn! {
    test_full_gp, rules(), 
    runner = 
        Runner::default()
        .with_node_limit(10000)
        .with_iter_limit(100)
        .with_time_limit(Duration::from_secs(10))
        .with_explanations_enabled(),
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

fn get_rewrites(e1 : &str, e2 : &str) {
    let mut graph = 
        EGraph::default()
        .with_explanations_enabled();

    let lhs : RecExpr<Optimization> = e1.parse().unwrap();
    let rhs : RecExpr<Optimization> = e2.parse().unwrap();

    let lhs_id = graph.add_expr(&lhs);
    let rhs_id = graph.add_expr(&rhs);

    let mut runner = 
        Runner::default()
        .with_egraph(graph)
        .with_explanations_enabled();
    runner = runner.run(&rules());

    let mut egraph = runner.egraph;

    if egraph.find(lhs_id) == egraph.find(rhs_id) {
        println!("Found equivalence!");
        let mut explanation : Explanation<Optimization> = 
            egraph.explain_equivalence(&lhs,&rhs);
        let flat_explanation : &FlatExplanation<Optimization> =
            explanation.make_flat_explanation();
        
        for i in 0..flat_explanation.len() {
            let expl = &flat_explanation[i];
            println!("Explanation: {}", expl.get_string());
            // if let Some(rule) = expl.forward_rule {
            //     println!("Rule: {} (FWD)", rule);
            // } else if let Some(rule) = expl.backward_rule {
            //     println!("Rule: {} (BWD)", rule);
            // }
        }
    }
}

// Test get list of rewrites easy expression.
#[test]
fn get_rewrites_easy() {
    get_rewrites(
        "(le (mul 3 (var x)) (var x))",
        "(le (mul 2 (var x)) 0)"
    )
}

// Test get list of rewrites from full geometric program.
#[test]
fn get_rewrites_full_gp() {
    get_rewrites(
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
        )",
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
                            (eq (sub (add (var x) (var y)) (var z)) 0.0)
                        )
                    )
                )
            )
        )")
}

#[derive(Debug)]
struct DCPScore<'a> {
    egraph: &'a EGraph,
    id : Id,
}

impl<'a> CostFunction<Optimization> for DCPScore<'a> {
    type Cost = usize;
    fn cost<C>(&mut self, _enode: &Optimization, mut _costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        // This doesn't work because curvature is not e-class invariant.
        let curvature = self.egraph[self.id].data.curvature.clone();
        if curvature == Curvature::Convex {
            return 0;
        }
        return 100;
    }
}

fn simplify(s: &str) -> String {
    let expr: RecExpr<Optimization> = s.parse().unwrap();

    let runner = Runner::default().with_expr(&expr).run(&rules());
    
    let root = runner.roots[0];
    
    println!("Number of nodes: {}", runner.egraph.total_number_of_nodes());
    println!("Number of e-classes: {}", runner.egraph.number_of_classes());

    let dot_str =  runner.egraph.dot().to_string();
    fs::write("test.dot", dot_str).expect("");

    let cost_func = DCPScore { egraph: &runner.egraph, id: root };
    let extractor = Extractor::new(&runner.egraph, cost_func);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);

    //print!("{}", runner.egraph);

    return best.to_string();
}

// Exp of log is a smal issue becuase we do that union and then apply log which is not class invariant.
#[test]
fn simple_tests() {
    let r = simplify("
    (prob 
        (objFun (var x)) 
        (constraints 
            (le 10.0 (mul (var x) (var x)))
        )
    )");
    println!("simplified: {}", r);
}

#[test]
fn simpler_tests() {
    let r = simplify("
    (mul (exp (var x)) (exp (var x)))");
    println!("simplified: {}", r);
}



#[test]
fn hard_test() {
    let r = simplify("(prob 
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
    )");
    println!("simplified: {}", r);
}