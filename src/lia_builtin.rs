pub mod lia_builtin{
    use std::{cell::{OnceCell, RefCell}, collections::HashMap, marker::PhantomData, rc::Rc, sync::Arc};

    use sexp::Error;
    use z3::ast::{Ast, Dynamic};

    use crate::{base::{function::{ExecError, PositionedExecutable}, language::{ConstraintPassesValue, DefineFun, Exp, SynthFun, Terms, Type}, scope::Scope}, parser::{self, parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser}, rc_function_var_context::{Command, RcFunctionVar}}};
    use crate::{lia_logic::lia::{Types, Values}};
    enum BuiltIn {
        Add,
        Sub,
        Eq,
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
    impl <Var> PositionedExecutable<Var, Values, Values> for BuiltIn {
        fn execute(&self, args: &Vec<Values>) -> Result<Values, ExecError> {
            let res = match self {
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
    
    pub fn get_empty_context_with_builtin<'a>() -> Context<'a, String, Values, Types> {
        let mut context = parser::rc_function_var_context::Context::<String, Values, Types>::new(None);
        context.add_and_set_function_var("+".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::Add)));
        context.add_and_set_function_var("-".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::Sub)));
        context.add_and_set_function_var("=".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::Eq)));
        context
    }
}