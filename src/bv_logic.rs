pub mod bv {
    use std::{cell::{OnceCell, RefCell}, collections::HashMap, marker::PhantomData, rc::Rc, sync::Arc};

    use sexp::{Error, Sexp};

    use crate::{base::{function::{ExecError, PositionedExecutable}, language::{ConstraintPassesValue, DefineFun, Exp, SynthFun, Terms, Type}, scope::Scope}, parser::{self, parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser}, rc_function_var_context::{Command, RcFunctionVar}}, z3_solver::Z3Solver};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Types {
        BV,
        Bool,
        Function
    }

    

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Values{
        BV(u64),
        Bool(bool),
    }

    
    impl AtomParser for Values {
        fn parse(input: &sexp::Atom) -> Result<Self, String> {
            // println!("Atom: {}", input);
            match input {
                sexp::Atom::I(i) => {
                    println!("I: {}", i);
                    Ok(Values::BV((*i).try_into().unwrap()))
                }
                sexp::Atom::S(s) => {
                    match s.chars().next() {
                        Some('#') => {
                            let hex_string = &s[2..];
                            match u64::from_str_radix(hex_string, 16) {
                                Ok(num) => Ok(Values::BV(num)),
                                Err(e) => Err(format!("Unknown value: {}", s))
                            }
                        }
                        _ => {
                            match s.as_str() {
                                "true" => Ok(Values::Bool(true)),
                                "false" => Ok(Values::Bool(false)),
                                _ => Err(format!("Unknown value: {}", s))
                            }
                        }
                    }

                },
                sexp::Atom::F(_) => Err("Floats are not supported".to_string())
            }
        }
        fn parse_list(input: &Vec<Sexp>) -> Result<Self, String> {
            Err("Values cannot be parsed from a list".to_string())
        }
    }

    impl ConstraintPassesValue for Values {
        fn is_pass(&self) -> bool {
            match self {
                Values::BV(_) => false,
                Values::Bool(v) => *v
            }
        }
    }

    impl Type for Types {
        fn from_identifier(identifier: &str) -> Option<Self> {
            match identifier {
                "BitVec" => Some(Types::BV),
                "Bool" => Some(Types::Bool),
                _ => None
            }
        }

        fn from_function(args: Vec<Self>, return_type: Self) -> Self {
            Types::Function
        }
    }

    use crate::parser::rc_function_var_context::Context;
    use crate::bv_builtin::bv_builtin::get_empty_context_with_builtin;

    fn test_lifetime<Context1>(ctx: &Context1) -> &Context1 
    where for<'a> Context1: Scope<String, Types, Values, RcFunctionVar<'a, String, Values>> {
        ctx
    }

    fn test_run(input: &Vec<sexp::Sexp>) -> Arc<Context<String, Values, Types>> {
        let mut context = get_empty_context_with_builtin();
        let mut defines: Vec<_> = Vec::new();
        for command in input {
            let res = Command::<String, Values, Types>::parse(command, &mut context);
            match res {
                Ok(c) => {
                    match c {
                        Command::DefineFun(d) => {
                            defines.push(d);
                        },
                        _ => ()
                    }
                },
                Err(e) => panic!("Error: {:?}", e)
            }
        }
        let rc_context = Arc::new(context);
        for define in defines {
            match define.context.set(rc_context.clone()) {
                Ok(_) => (),
                Err(_) => panic!("Error")   // 不应出现
            }
        }
        rc_context
    } 
    #[test]
    fn simple_test() {
        // let code = "((define-fun shr1 ((x (_ BitVec 64))) (_ BitVec 64) (bvlshr x #x0000000000000001)))";
        let code = "((define-fun if0 ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) (_ BitVec 64) (ite (= x #x0000000000000001) y z)))";
        // let code = "((define-fun add ((x Int) (y Int)) Int (+ (mod x 2) y)))";
        let input = sexp::parse(code).unwrap();
        // println!("Input: {:?}", input);
        match input {
            sexp::Sexp::List(v) => {
                let final_ctx = test_run(&v);
                final_ctx.get_value(&"ite".to_string()).unwrap().expect_right("error");
                final_ctx.get_value(&"=".to_string()).unwrap().expect_right("error");
                let f = final_ctx.get_value(&"if0".to_string()).unwrap().expect_right("error");
                let res = f.execute(&vec![Values::BV(1), Values::BV(2), Values::BV(3)]).unwrap();
                // println!("Result: {:?}", res);
                assert_eq!(res, Values::BV(2));
            },
            _ => panic!("Expected a list")
        }
        ;
    }

    // #[test]
    // fn test_z3_solver() {
    //     use crate::lia_logic::lia::{Types, Values};
    //     let ctx = z3::Context::new(&Default::default());

    //     let define_fun = DefineFun {
    //         var_index: "g".to_string(),
    //         args: vec![("x".to_string(), Types::Int)],
    //         context: OnceCell::<Arc<Context<String, Values, Types>>>::new(),
    //         return_type: Types::Int,
    //         body: Exp::Value(Terms::<String, Values>::Var("x".to_string())),
    //         _phantom: PhantomData::<RcFunctionVar<'_, String, Values>>,
    //     };
        
    // }
}