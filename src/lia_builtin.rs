pub mod lia_builtin {
    use std::{
        cell::{OnceCell, RefCell},
        collections::HashMap,
        fmt::Debug,
        marker::PhantomData,
        rc::Rc,
        sync::Arc,
    };

    use either::Either;
    use sexp::Error;
    use z3::ast::{Ast, Dynamic};

    use crate::{base::language::BasicFun, lia_logic::lia::{Types, Values}};
    use crate::{
        base::{
            function::{ExecError, GetValueError, PositionedExecutable},
            language::{Constraint, ConstraintPassesValue, DefineFun, Exp, SynthFun, Terms, Type},
            scope::Scope,
        },
        parser::{
            self,
            parser::{AtomParser, ContextFreeSexpParser, MutContextSexpParser},
            rc_function_var_context::{Command, RcFunctionVar},
        },
    };
    enum BuiltIn {
        Add,
        Sub,
        Eq,
        MUL,
        MOD,
        GT,
        LT,
        GE,
        LE,
        AND,
        OR,
        NOT,
        ITE,
        Impl,
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
            return Err(ExecError::TypeMismatch(format!(
                "Expected {} arguments in {}, got {}",
                expected,
                name,
                args.len()
            )));
        }
        Ok(())
    }
    impl<Var> PositionedExecutable<Var, Values, Values> for BuiltIn {
        fn execute(&self, args: &Vec<Values>) -> Result<Values, ExecError> {
            let res = match self {
                BuiltIn::Add => {
                    arg_num_check(&args, 2, "Add")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => {
                            Ok(Values::Int(i64::wrapping_add(a, b)))
                        }
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in Add, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::Sub => {
                    arg_num_check(&args, 2, "Sub")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => {
                            Ok(Values::Int(i64::wrapping_sub(a, b)))
                        }
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in Sub, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::Eq => {
                    arg_num_check(&args, 2, "Eq")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a == b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in Eq, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::MOD => {
                    arg_num_check(&args, 2, "MOD")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(0)) => Err(ExecError::DivZero),
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Int(a % b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in MOD, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::MUL => {
                    arg_num_check(&args, 2, "MUL")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => {
                            Ok(Values::Int(i64::wrapping_mul(a, b)))
                        }
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in MUL, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::GT => {
                    arg_num_check(&args, 2, "GT")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a > b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in GT, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::LT => {
                    arg_num_check(&args, 2, "LT")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a < b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in LT, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::GE => {
                    arg_num_check(&args, 2, "GE")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a >= b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in GE, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::LE => {
                    arg_num_check(&args, 2, "LE")?;
                    match (args[0], args[1]) {
                        (Values::Int(a), Values::Int(b)) => Ok(Values::Bool(a <= b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Int, Int in LE, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::AND => {
                    arg_num_check(&args, 2, "AND")?;
                    match (args[0], args[1]) {
                        (Values::Bool(a), Values::Bool(b)) => Ok(Values::Bool(a && b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Bool, Bool in AND, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::OR => {
                    arg_num_check(&args, 2, "OR")?;
                    match (args[0], args[1]) {
                        (Values::Bool(a), Values::Bool(b)) => Ok(Values::Bool(a || b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Bool, Bool in OR, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
                    }
                }
                BuiltIn::NOT => {
                    arg_num_check(&args, 1, "NOT")?;
                    match args[0] {
                        Values::Bool(a) => Ok(Values::Bool(!a)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Bool in NOT, got {:?}",
                            args[0]
                        ))),
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
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Bool in ITE, got {:?}",
                            args[0]
                        ))),
                    }
                }
                BuiltIn::Impl => {
                    arg_num_check(&args, 2, "Impl")?;
                    match (args[0], args[1]) {
                        (Values::Bool(a), Values::Bool(b)) => Ok(Values::Bool(!a || b)),
                        _ => Err(ExecError::TypeMismatch(format!(
                            "Expected Bool, Bool in Impl, got {:?}, {:?}",
                            args[0], args[1]
                        ))),
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
        let mut context =
            parser::rc_function_var_context::Context::<String, Values, Types>::new(None);
        context.add_and_set_function_var(
            "+".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::Add)),
        );
        context.add_and_set_function_var(
            "-".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::Sub)),
        );
        context.add_and_set_function_var(
            "=".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::Eq)),
        );
        context.add_and_set_function_var(
            "mod".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::MOD)),
        );
        context.add_and_set_function_var(
            "*".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::MUL)),
        );
        context.add_and_set_function_var(
            ">".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::GT)),
        );
        context.add_and_set_function_var(
            "<".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::LT)),
        );
        context.add_and_set_function_var(
            ">=".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::GE)),
        );
        context.add_and_set_function_var(
            "<=".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::LE)),
        );
        context.add_and_set_function_var(
            "and".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::AND)),
        );
        context.add_and_set_function_var(
            "or".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::OR)),
        );
        context.add_and_set_function_var(
            "not".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::NOT)),
        );
        context.add_and_set_function_var(
            "ite".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::ITE)),
        );
        context.add_and_set_function_var(
            "=>".to_string(),
            Types::Function,
            RcFunctionVar(Arc::new(BuiltIn::Impl)),
        );
        context
    }
}
