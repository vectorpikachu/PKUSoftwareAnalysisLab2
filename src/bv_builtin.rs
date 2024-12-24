pub mod bv_builtin{
    use std::{cell::{OnceCell, RefCell}, collections::HashMap, fmt::Debug, marker::PhantomData, rc::Rc, sync::Arc};

    use sexp::Error;
    use z3::ast::{Ast, Dynamic};

    use crate::{base::{function::{ExecError, PositionedExecutable}, language::{ConstraintPassesValue, DefineFun, Exp, SynthFun, Terms, Type}, scope::Scope}, parser::{self, parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser}, rc_function_var_context::{Command, RcFunctionVar}}};
    use crate::{bv_logic::bv::{Types, Values}};
    enum BuiltIn {
        Eq,
        ITE,
        BVNOT,
        BVAND,
        BVOR,
        BVXOR,
        BVADD,
        BVLSHR,
        BVSHL,
    }
    fn omit_error_unless_debug<V, E: Debug>(v: Result<V, E>) -> Result<V, E> {
        if cfg!(debug_assertions) {
            v
        } else {
            match v {
                Ok(v) => Ok(v),
                Err(e) => panic!("{:?}", e),
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
                BuiltIn::Eq => {
                    arg_num_check(&args, 2, "Eq")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::Bool(a == b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in Eq, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::BVNOT => {
                    arg_num_check(&args, 2, "BVNOT")?;
                    match args[0] {
                        Values::BV(a) => Ok(Values::BV(!a)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV in BVNOT, got {:?}", args[0])))
                    }
                }
                BuiltIn::BVAND => {
                    arg_num_check(&args, 2, "BVAND")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a & b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVAND, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::BVOR => {
                    arg_num_check(&args, 2, "BVOR")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a | b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVOR, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::BVXOR => {
                    arg_num_check(&args, 2, "BVXOR")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a ^ b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVXOR, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::BVADD => {
                    arg_num_check(&args, 2, "BVADD")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a.wrapping_add(b))),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVADD, got {:?}, {:?}", args[0], args[1])))
                    }   
                }
                BuiltIn::BVLSHR => {
                    arg_num_check(&args, 2, "BVLSHR")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a >> b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVLSHR, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::BVSHL => {
                    arg_num_check(&args, 2, "BVSHL")?;
                    match (args[0], args[1]) {
                        (Values::BV(a), Values::BV(b)) => Ok(Values::BV(a << b)),
                        _ => Err(ExecError::TypeMismatch(format!("Expected BV, BV in BVSHL, got {:?}, {:?}", args[0], args[1])))
                    }
                }
                BuiltIn::ITE => {
                    arg_num_check(&args, 3, "ITE")?;
                    match args[0] {
                        Values::Bool(b) => {
                            if b {
                                Ok(args[1].clone())
                            } else {
                                Ok(args[2].clone())
                            }
                        }
                        _ => Err(ExecError::TypeMismatch(format!("Expected Bool in ITE, got {:?}", args[0])))
                    }
                }
            };
            res
            // if let Err(ExecError::DivZero) = res {
            //     return Err(ExecError::DivZero);
            // }
            // omit_error_unless_debug(res) // 由于除零问题，这里不能忽略错误
        }
    }
    use parser::rc_function_var_context::Context;
    pub fn get_empty_context_with_builtin<'a>() -> Context<'a, String, Values, Types> {
        let mut context = parser::rc_function_var_context::Context::<String, Values, Types>::new(None);
        context.add_and_set_function_var("=".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::Eq)));
        context.add_and_set_function_var("ite".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::ITE)));
        context.add_and_set_function_var("bvnot".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVNOT)));
        context.add_and_set_function_var("bvand".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVAND)));
        context.add_and_set_function_var("bvor".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVOR)));
        context.add_and_set_function_var("bvxor".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVXOR)));
        context.add_and_set_function_var("bvadd".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVADD)));
        context.add_and_set_function_var("bvlshr".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVLSHR)));
        context.add_and_set_function_var("bvshl".to_string(), Types::Function, RcFunctionVar(Arc::new(BuiltIn::BVSHL)));
        context
    }
}