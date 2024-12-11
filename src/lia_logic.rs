pub mod lia {
    use std::{cell::RefCell, rc::Rc, sync::Arc};

    use sexp::Error;

    use crate::{base::{function::{ExecError, PositionedExecutable}, language::Type, scope::Scope}, parser::{self, parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser}, rc_function_var_context::{Command, RcFunctionVar}}};

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Types {
        Int,
        Bool,
        Function
    }
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Values{
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

    enum BuiltIn {
        Add,
        Sub,
        Eq,
    }
    struct BuiltInFun {
        tag: BuiltIn,
    }
    fn omit_error_unless_debug<V, E>(v: Result<V, E>) -> Result<V, E> {
        if cfg!(debug_assertions) {
            v
        } else {
            match v {
                Ok(v) => Ok(v),
                Err(_) => panic!()
            }
        }
    }
    fn arg_num_check(args: &Vec<Values>, expected: usize, name: &str) -> Result<(), ExecError> {
        if args.len() != expected {
            return Err(ExecError::TypeMismatch(format!("Expected {} arguments in {}, got {}", expected, name, args.len())));
        }
        Ok(())
    }
    impl <Var> PositionedExecutable<Var, Values, Values> for BuiltInFun {
        fn execute(&self, args: Vec<Values>) -> Result<Values, ExecError> {
            let res = match self.tag {
                BuiltIn::Add => {
                    arg_num_check(&args, 2, "Add")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Int(a + b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected Int, Int in Add, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::Sub => {
                    arg_num_check(&args, 2, "Sub")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Int(a - b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected Int, Int in Sub, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::Eq => {
                    arg_num_check(&args, 2, "Eq")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a == b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected Int, Int in Eq, got {:?}, {:?}", args[0], args[1])))
                    }
                }
            };
            omit_error_unless_debug(res)
        }
    }
    use parser::rc_function_var_context::Context;
    fn get_empty_context_with_builtin<'a>() -> Context<'a, String, Values, Types> {
        let mut context = parser::rc_function_var_context::Context::<String, Values, Types>::new(None);
        context.add_and_set_function_var("+".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltInFun{tag: BuiltIn::Add})));
        context.add_and_set_function_var("-".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltInFun{tag: BuiltIn::Sub})));
        context.add_and_set_function_var("=".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltInFun{tag: BuiltIn::Eq})));
        context
    }
    fn test_fun(ctx: &mut Context<String, Values, Types>, input: &str) -> () {
        ()
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
        let code = "((define-fun add ((x Int) (y Int)) Int (+ (+ x 1) y)))";
        let input = sexp::parse(code).unwrap();
        match input {
            sexp::Sexp::List(v) => {
                let final_ctx = test_run(&v);
                final_ctx.get_value("+".to_string()).unwrap().expect_right("error");
                let f = final_ctx.get_value("add".to_string()).unwrap().expect_right("error");
                let res = f.execute(vec![Values::Int(1), Values::Int(2)]).unwrap();
                assert_eq!(res, Values::Int(4));
            },
            _ => panic!("Expected a list")
        }
        ;
    }

}