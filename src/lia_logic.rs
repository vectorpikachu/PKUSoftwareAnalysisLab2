pub mod lia {
    use std::{cell::{OnceCell, RefCell}, collections::HashMap, marker::PhantomData, rc::Rc, sync::Arc};

    use sexp::Error;
    use z3::ast::{Ast, Dynamic};

    use crate::{base::{function::{ExecError, PositionedExecutable}, language::{ConstraintPassesValue, DefineFun, Exp, SynthFun, Terms, Type}, scope::Scope}, parser::{self, parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser}, rc_function_var_context::{Command, RcFunctionVar}}};

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Types {
        Int,
        Bool,
        Function
    }

    

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Values{
        Int(i64),
        Bool(bool),
    }

    
    impl AtomParser for Values {
        fn parse(input: &sexp::Atom) -> Result<Self, String> {
            match input {
                sexp::Atom::I(i) => Ok(Values::Int(*i)),
                // 注意本次作业似乎没有 Bool 字面量
                sexp::Atom::S(s) => {
                    match s.as_str() {
                        "true" => Ok(Values::Bool(true)),
                        "false" => Ok(Values::Bool(false)),
                        _ => Err(format!("Unknown value: {}", s))
                    }
                },
                sexp::Atom::F(_) => Err("Floats are not supported".to_string())
            }
        }
    }

    impl ConstraintPassesValue for Values {
        fn is_pass(&self) -> bool {
            match self {
                Values::Int(_) => false,
                Values::Bool(v) => *v
            }
        }
    }

    impl Type for Types {
        fn from_identifier(identifier: &str) -> Option<Self> {
            match identifier {
                "Int" => Some(Types::Int),
                "Bool" => Some(Types::Bool),
                _ => None
            }
        }

        fn from_function(args: Vec<Self>, return_type: Self) -> Self {
            Types::Function
        }
    }

    use crate::parser::rc_function_var_context::Context;
    use crate::lia_builtin::lia_builtin::get_empty_context_with_builtin;
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
        let code = "((define-fun add ((x Int) (y Int)) Int (+ (+ x 1) y)))";
        let input = sexp::parse(code).unwrap();
        match input {
            sexp::Sexp::List(v) => {
                let final_ctx = test_run(&v);
                final_ctx.get_value(&"+".to_string()).unwrap().expect_right("error");
                let f = final_ctx.get_value(&"add".to_string()).unwrap().expect_right("error");
                let res = f.execute(&vec![Values::Int(1), Values::Int(2)]).unwrap();
                assert_eq!(res, Values::Int(4));
            },
            _ => panic!("Expected a list")
        }
        ;
    }


}