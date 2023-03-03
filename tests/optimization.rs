use egg::{rewrite as rw, *};

define_language! {
    pub enum Optimization {
        // Main structure
        "prob" = Prob([Id; 2]),
        "objFun" = ObjFun(Id),
        "constraints" = Constraints(Id),
        
        // Logic
        "and" = And([Id; 2]),
        "app" = App([Id; 2]),
        "comp" = Comp([Id; 2]),
        "fun" = Fun([Id; 2]),
        "const" = Const(Id), 
        "var" = Var(Symbol),

        // Comparison
        "eq" = Eq([Id; 2]),
        "le" = Le([Id; 2]),

        // Arithmetic
        "neg" = Neg(Id),
        "add" = Add([Id; 2]),
        "mul" = Mul([Id; 2]),
        "pow" = Pow([Id; 2]),
        "log" = Log(Id),
        "exp" = Exp(Id),

        // Variables
        Symbol(Symbol),

        // Constants
        Float(u64),
        Bool(bool),
    }
}

pub fn rules() -> Vec<Rewrite<Optimization, ()>> { vec![
    rw! { "and-comm"; "(and ?a ?b)" => "(and ?b ?a)" },
    rw! { "and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))" },
    rw! { "and-assoc-2"; "(and ?a (and ?b ?c))" => "(and (and ?a ?b) ?c)" },
    rw! { "and-true"; "(and ?a true)" => "?a" },
    rw! { "and-false"; "(and ?a false)" => "false" },
    
    rw! { "app-const"; "(app (fun ?x (const ?c)) ?y)" => "(const ?c)" },
    rw! { "app-id"; "(app (fun ?x ?x) ?y)" => "?y" },
    rw! { "beta"; "(app (fun ?x ?y) ?x)" => "?y" },
    rw! { "app-and"; "(app (fun ?x (and ?a ?b)) ?y)" => "(and (app (fun ?x ?a) ?y) (app (fun ?x ?b) ?y))" },
    rw! { "app-le"; "(app (fun ?x (le ?a ?b)) ?y)" => "(le (app (fun ?x ?a) ?y) (app (fun ?x ?b) ?y))" },
    rw! { "app-neg"; "(app (fun ?x (neg ?a)) ?y)" => "(neg (app (fun ?x ?a) ?y))" },
    rw! { "app-add"; "(app (fun ?x (add ?a ?b)) ?y)" => "(add (app (fun ?x ?a) ?y) (app (fun ?x ?b) ?y))" },
    rw! { "app-mul"; "(app (fun ?x (mul ?a ?b)) ?y)" => "(mul (app (fun ?x ?a) ?y) (app (fun ?x ?b) ?y))" },
    rw! { "app-pow"; "(app (fun ?x (pow ?a ?b)) ?y)" => "(pow (app (fun ?x ?a) ?y) (app (fun ?x ?b) ?y))" },
    rw! { "app-log"; "(app (fun ?x (log ?a)) ?y)" => "(log (app (fun ?x ?a) ?y))" },
    rw! { "app-exp"; "(app (fun ?x (exp ?a)) ?y)" => "(exp (app (fun ?x ?a) ?y))" },

    rw! { "comp-const"; "(comp (fun ?x ?f) (const ?c))" => "(fun ?x (const ?c))" },
    rw! { "comp-and"; 
            "(comp (fun ?x (and ?a ?b)) (fun ?y ?f))" => 
            "(fun ?x (and (app (fun ?y ?f) ?a) (app (fun ?y ?f) ?b)))" },
    rw! { "comp-le";
            "(comp (fun ?x (le ?a ?b)) (fun ?y ?f))" => 
            "(fun ?x (le (app (fun ?y ?f) ?a) (app (fun ?y ?f) ?b)))" },
    rw! { "comp-neg";
            "(comp (fun ?x (neg ?a)) (fun ?y ?f))" => 
            "(fun ?x (neg (app (fun ?y ?f) ?a)))" },
    rw! { "comp-add"; 
            "(comp (fun ?x (add ?a ?b)) (fun ?y ?f))" => 
            "(fun ?x (add (app (fun ?y ?f) ?a) (app (fun ?y ?f) ?b)))" },
    rw! { "comp-mul";
            "(comp (fun ?x (mul ?a ?b)) (fun ?y ?f))" => 
            "(fun ?x (mul (app (fun ?y ?f) ?a) (app (fun ?y ?f) ?b)))" },
    rw! { "comp-pow";
            "(comp (fun ?x (pow ?a ?b)) (fun ?y ?f))" => 
            "(fun ?x (pow (app (fun ?y ?f) ?a) (app (fun ?y ?f) ?b)))" }, 
    rw! { "comp-log";
            "(comp (fun ?x (log ?a)) (fun ?y ?f))" => 
            "(fun ?x (log (app (fun ?y ?f) ?a)))" },
    rw! { "comp-exp";
            "(comp (fun ?x (exp ?a)) (fun ?y ?f))" => 
            "(fun ?x (exp (app (fun ?y ?f) ?a)))" },
    rw! { "comp-exp-2";
            "(comp (fun ?x ?f) (fun ?y (exp ?a)))" =>
            "(fun ?x (exp (app (fun ?y ?a) ?f)))" },

    rw! { "neg-zero" ; "(neg 0)" => "0" },
    rw! { "neg-neg"; "(neg (neg ?a))" => "?a" },
    rw! { "neg-add-distrib"; "(add (neg ?a) (neg ?b))" => "(neg (add ?a ?b))" },//
    rw! { "neg-mul-left"; "(mul (neg ?a) ?b)" => "(neg (mul ?a ?b))" },//
    rw! { "neg-mul-right"; "(mul ?a (neg ?b))" => "(neg (mul ?a ?b))" },//
    rw! { "neg-mul-left-right"; "(mul (neg ?a) (neg ?b))" => "(mul ?a ?b)" },//

    rw! { "add-0"; "(add ?a 0)" => "?a" },
    rw! { "add-comm"; "(add ?a ?b)" => "(add ?b ?a)" },
    rw! { "add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))" },//

    rw! { "mul-0"; "(mul ?a 0)" => "0" },
    rw! { "mul-1"; "(mul ?a 1)" => "?a" },
    rw! { "mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)" },
    rw! { "mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))" },//
    rw! { "mul-add-distrib"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))" },//

    rw! { "pow-0"; "(pow ?a 0)" => "1" },
    rw! { "pow-1"; "(pow ?a 1)" => "?a" },
    rw! { "pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))" },//

    rw! { "log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" },//
    rw! { "log-pow"; "(log (pow ?a ?b))" => "(mul ?b (log ?a))" },
    rw! { "mul-log"; "(mul ?b (log ?a))" => "(log (pow ?a ?b))" },
    rw! { "log-exp"; "(log (exp ?a))" => "?a" },
    rw! { "le-of-log-le"; "(le (log ?a) (log ?b))" => "(le ?a ?b)" },
    rw! { "log-le-of-le"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" },

    rw! { "exp-log"; "(exp (log ?a))" => "?a" },
    rw! { "exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))" },
    rw! { "mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))" },
    
    rw! { "prob-map-exp"; 
            "(prob (objFun ?o) (constraints ?cs))" => 
            "(prob (objFun (comp ?o (fun (var ?x) (exp ?x)) ) ) (constraints (comp ?cs (fun (var ?y) (exp ?y)) ) ) )" },
]}

egg::test_fn! {
    test_1, rules(),
    "(prob 
        (objFun 
            (fun x x)
        ) 
        (constraints 
            (fun x (le (const 0) x))
        )
    )" => 
    "(prob 
        (objFun 
            (comp 
                (fun x x) 
                (fun y (exp y)) 
            )
        ) 
        (constraints 
            (comp 
                (fun x (le (const 0) x)) 
                (fun y (exp y))
            )
        )
    )"
}
