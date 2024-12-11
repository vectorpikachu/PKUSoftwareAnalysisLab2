pub mod function {
    use std::collections::HashMap;

    use either::Either;

    pub enum GetValueError {
        VarNotDefined(String),
        VarNotAssigned(String)
    }
    pub enum ExecError {
        VarNotDefined(String),
        VarNotAssigned(String),
        TypeMismatch(String)
    }
    /// 无上下文，可按位置执行的函数
    pub trait PositionedExecutable<Var, Terms, ReturnType> {
        /// 如果有参数未赋值，返回 None
        fn execute (
            &self, 
            args: Vec<Terms>,
        ) -> Result<ReturnType, ExecError>;
    }
    /// 可以按照参数名调用的函数
    pub trait NamedExecutable<
        Identifier, 
        Values, 
        FunctionVar: PositionedExecutable<Identifier, Values, Values>, 
        ReturnType> {
        /// 如果有参数未赋值，返回 None
        /// 注意这里的 PositionedExecutable 是代表变量既可能是值，也可能是函数变量
        fn execute<F: Fn(Identifier) -> Result<Either<Values, FunctionVar>, GetValueError> + Copy> (
            &self, 
            args_map: F
        ) -> Result<ReturnType, ExecError>;
    }
    
    pub trait ExplicitParameter<Var, Types> {
        fn get_args(&self) -> impl Iterator<Item = (Var, Types)>;
    }

    // use std::hash::Hash;
    // impl <Var: Eq + Hash, Types, Terms: Clone,
    //  F: NamedExecutable<Var, Types, Terms> + ExplicitParameter<Var, Types>> 
    //     PositionedExecutable<Var, Types, Terms> for F {
    //     fn execute (
    //         &self, 
    //         mut args: Vec<Terms>
    //     ) -> Result<Terms, ExecError> {
    //         let mut arg_hash_map: HashMap<Var, Terms> = HashMap::new();
    //         for (var, _) in self.get_args() {
    //             arg_hash_map.insert(var, args.pop().ok_or(ExecError::VarNotDefined)?);
    //         }
    //         self.execute(|var| arg_hash_map.get(&var).cloned().ok_or(GetValueError::VarNotDefined))
    //     }
    // }

    pub trait VarIndex: Clone {
        fn to_name(&self) -> String;
        fn from_name(name: String) -> Self;
    }

    impl VarIndex for String {
        fn to_name(&self) -> String {
            self.clone()
        }
        fn from_name(name: String) -> Self {
            name
        }
    }
    
    #[derive(Clone, Copy)]
    struct BoxFunctionVar<'a, Identifier, PrimValues> {
        f: &'a Box<dyn PositionedExecutable<Identifier, PrimValues, PrimValues>>,
    }

    // /// 函数变量，包括内建函数和 define-fun 函数
    // pub trait FunctionVar<Var: VarIndex, Types, Terms>: ExecutableFunction<Var, Types, Terms> {
    //     fn get_var_index(&self) -> Var;
    //     fn get_name(&self) -> String {
    //         self.get_var_index().to_name()
    //     }
    // }
    // /// 内建函数
    pub trait BuiltinFunction<Var: VarIndex, Values, ReturnType>: PositionedExecutable<Var, Values, ReturnType> {
        fn from_name(name: String) -> Option<&'static Self>;
    }
    // /// define-fun 函数
    // pub trait DefinedFunction<Var: VarIndex, Types, Terms>: FunctionVar<Var, Types, Terms> {
    // }
}

pub mod logic {
    use sexp::Atom;

    // 支持的理论
    enum LogicTag {
        LIA,
        BV 
    }
    impl LogicTag {
        fn to_string(&self) -> &'static str {
            match self {
                LogicTag::LIA => "LIA",
                LogicTag::BV => "BV"
            }
        }
    }
    fn parse_logic_tag(exp: Atom) -> LogicTag {
        match exp {
            Atom::S(s) => {
                match s.as_str() {
                    "LIA" => LogicTag::LIA,
                    "BV" => LogicTag::BV,
                    _ => panic!("Unsupported logic")
                }
            },
            _ => panic!("Unsupported logic")
        }
    }

    use super::function::{BuiltinFunction, VarIndex};
    
    /// 其中 Types 是语言中的类型，Values 是语言中的值
    pub trait Logic {
        type Types;
        type Values;
        fn get_type_of_value(&self, value: &Self::Values) -> Self::Types;
        fn get_builtin_function_from_index<Var: VarIndex> (&self, index: Var) -> impl BuiltinFunction<Var, Self::Values, Self::Values>;
        fn get_builtin_function_from_name<Var: VarIndex> (&self, name: String) -> impl BuiltinFunction<Var, Self::Values, Self::Values> {
            self.get_builtin_function_from_index(VarIndex::from_name(name))
        }
    }

}

pub mod scope {
    use std::collections::HashMap;
    use std::hash::Hash;
    use std::fmt::Debug;
    use either::Either;

    use super::function::{ExecError, NamedExecutable, GetValueError, PositionedExecutable};
    /// 表示当前函数体内的上下文。
    /// 我们将变量分为两类，已经赋值的和未赋值的。
    pub trait Scope<Identifier, Types, Values, FunctionVar: PositionedExecutable<Identifier, Values, Values>> {
        /// 获取当前作用域内的所有变量及其类型的迭代器，注意只会返回当前 Scope 内的而不会返回上层 Scope 的变量
        fn get_all_vars(&self) -> impl Iterator<Item = (Identifier, Types)>;

        /// 获取当前作用域内的变量类型，None 表示无这个变量。只能获取非函数变量
        fn get_type(&self, var: Identifier) -> Option<Types>;

        /// 获取当前作用域内的变量值，优先返回本层的，如果本层没有则返回上层的
        fn get_value(&self, var: Identifier) -> Result<Either<Values, FunctionVar>, GetValueError>;

        /// 设置当前作用域内的变量值，返回是否设置成功。只能设置本层的非函数变量
        fn set_value(&mut self, var: Identifier, value: Values) -> Option<()>;
        
        /// 设置当前作用域内的函数变量值，返回是否设置成功。只能设置本层的函数变量
        fn set_function_var(&mut self, var: Identifier, value: FunctionVar) -> Option<()>;

        // 在当前 scope 下执行函数
        fn execute_in<ResultType>(&self, f: impl NamedExecutable<Identifier, Values, FunctionVar, ResultType>) -> Result<ResultType, ExecError> {
            f.execute(|var| self.get_value(var))
        }
    }
    pub struct ScopeImpl<'a, Identifier, Types, Values, FunctionVar: PositionedExecutable<Identifier, Values, Values>> {
        pub all_vars: HashMap<Identifier, Types>,
        pub non_function_vars: HashMap<Identifier, Values>,
        pub function_vars: HashMap<Identifier, FunctionVar>,
        pub parent_scope: Option<&'a ScopeImpl<'a, Identifier, Types, Values, FunctionVar>>,
    }
    impl <'a, Identifier: Eq + Hash + Copy + Debug, Types: Copy, Values: Copy, FunctionVar: PositionedExecutable<Identifier, Values, Values> + Copy> Scope<Identifier, Types, Values, FunctionVar> for ScopeImpl<'a, Identifier, Types, Values, FunctionVar> {
        fn get_all_vars(&self) -> impl Iterator<Item = (Identifier, Types)> {
            self.all_vars.iter().map(|(k, v)| (*k, *v))
        }
        fn get_type(&self, var: Identifier) -> Option<Types> {
            self.all_vars.get(&var).copied()
        }
        fn get_value(&self, var: Identifier) -> Result<Either<Values, FunctionVar>, GetValueError> {
            if let Some(value) = self.non_function_vars.get(&var) {
                Ok(Either::Left(*value))
            } else if let Some(value) = self.function_vars.get(&var) {
                Ok(Either::Right(*value))
            } else {
                match self.parent_scope {
                    Some(parent) => parent.get_value(var),
                    None => Err(GetValueError::VarNotDefined(format!("{:?}", var)))
                }
            }
        }
        fn set_value(&mut self, var: Identifier, value: Values) -> Option<()> {
            if self.all_vars.contains_key(&var) {
                self.non_function_vars.insert(var, value);
                Some(())
            } else {
                None
            }
        }
        fn set_function_var(&mut self, var: Identifier, value: FunctionVar) -> Option<()> {
            if self.all_vars.contains_key(&var) {
                self.function_vars.insert(var, value);
                Some(())
            } else {
                None
            }
        }
    }

}

pub mod language {
    use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

    use either::Either;

    use super::{function::{BuiltinFunction, ExecError, ExplicitParameter, GetValueError, NamedExecutable, PositionedExecutable, VarIndex}, scope::{self, Scope}};


    #[derive(Debug, Clone)]
    pub enum Terms<Var: Clone, PrimValues: Copy> {
        Var(Var),
        PrimValue(PrimValues),
    }

    // impl <
    //     Var: Copy + Debug + VarIndex, 
    //     PrimValues,
    //     PrimFunction: BuiltinFunction<Var, PrimValues, PrimValues, PrimValues>       
    //     > PositionedExecutable<Var, Terms<Var, PrimValues>, PrimValues> for Terms<Var, PrimValues>
    // where
    //     PrimValues: Copy + PositionedExecutable<Var, PrimValues, PrimValues>
    //     {
    //     fn execute (
    //         &self, 
    //         args: Vec<Terms<Var, PrimValues>>
    //     ) -> Result<PrimValues, ExecError> {
    //         match self {
    //             Terms::Var(x) => Err(ExecError::VarNotDefined(format!("{:?}", x))),
    //             Terms::PrimValue(value) => {
    //                 let args1 = args.iter().map(|x| match x {
    //                     Terms::Var(var) => Err(ExecError::VarNotDefined(format!("{:?}", var))),
    //                     Terms::PrimValue(value) => Ok(*value)
    //                 }).collect::<Result<Vec<_>, _>>()?;
    //                 PositionedExecutable::execute(value, args1)
    //             }
    //         }
    //     }
    // }

    // 由于本次作业似乎不需要，因此这里 Exp 就不带类型了
    #[derive(Debug)]
    pub enum Exp<Identifier: Clone, PrimValues: Copy> {
        Value(Terms<Identifier, PrimValues>),
        Apply(Identifier, Vec<Exp<Identifier, PrimValues>>),   // 注意我们使用的语言中，函数应用中的函数只能是 Identifier
    } 
    
    impl <
        Identifier: VarIndex + Clone + Debug, 
        PrimValues: Copy + Debug,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Copy,
        > 
    NamedExecutable<Identifier, PrimValues, FunctionVar, PrimValues> for Exp<Identifier, PrimValues> {
        /// 注意我们允许零个参数的 FunctionVar
        fn execute<F: Fn(Identifier) -> Result<Either<PrimValues, FunctionVar>, GetValueError> + Copy> (
            &self, 
            args_map: F
        ) -> Result<PrimValues, ExecError> {
            match self {
                Exp::Value(value) => {
                    match value {
                        Terms::Var(var) => {
                            match args_map(var.clone()) {
                                Ok(Either::Left(x)) => Ok(x),
                                Ok(Either::Right(f)) => f.execute(vec![]),
                                Err(GetValueError::VarNotAssigned(s)) => Err(ExecError::VarNotAssigned(s)),
                                Err(GetValueError::VarNotDefined(s)) => Err(ExecError::VarNotDefined(s))
                        }
                        },
                        Terms::PrimValue(value) => Ok(*value)
                    }
                },
                Exp::Apply(f, args) => {
                    let f = match args_map(f.clone()) {
                        Ok(Either::Left(x)) => return Err(ExecError::TypeMismatch(format!("{:?}", x))),
                        Ok(Either::Right(f)) => f,
                        Err(GetValueError::VarNotAssigned(s)) => return Err(ExecError::VarNotAssigned(s)),
                        Err(GetValueError::VarNotDefined(s)) => return Err(ExecError::VarNotDefined(s))
                    };
                    let args = args.iter().map(|x| x.execute(args_map)).collect::<Result<Vec<_>, _>>()?;
                    f.execute(args)
                }
            }
        }
    }

    // trait ContextFree {}

    // pub struct IsContextFree;
    // pub struct NotContextFree;
    // impl ContextFree for IsContextFree {}
    #[derive(Debug)]
    pub struct DefineFun<
        'a,
        Identifier: VarIndex + Clone, 
        PrimValues: Copy, Types, 
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues>,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > {
        pub name: String,
        pub var_index: Identifier,
        pub args: Vec<(Identifier, Types)>,
        pub context: &'a Context,
        pub return_type: Types,
        pub body: Exp<Identifier, PrimValues>,
        _phantom: PhantomData<FunctionVar>
    }

    // #[derive(Clone, Copy)]
    // struct EmptyFunctionVar {}
    // impl <Identifier, PrimValues, ReturnType> PositionedExecutable<Identifier, PrimValues, ReturnType> for EmptyFunctionVar {
    //     fn execute (
    //         &self, 
    //         args: Vec<PrimValues>
    //     ) -> Result<ReturnType, ExecError> {
    //         panic!("EmptyFunctionVar should not be executed")
    //     }
    // }

    // impl <
    //     'a,
    //     Identifier: VarIndex + Clone + Eq + Hash + Debug, 
    //     PrimValues: Copy + Debug, 
    //     Types,
    //     FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Copy,
    //     Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    // >
    //     ExplicitParameter<Identifier, PrimValues> 
    //         for DefineFun<'a, Identifier, PrimValues, Types, FunctionVar, Context>
    //     {
    //     fn get_args(&self) -> impl Iterator<Item = (Identifier, Types)> {
    //         self.args.iter().copied()
    //     }
    // }

    impl <
        'a,
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug, 
        Types,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Copy,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > 
        PositionedExecutable<Identifier, PrimValues, PrimValues> 
            for DefineFun<'a, Identifier, PrimValues, Types, FunctionVar, Context> {
        /// 注意我们的执行规则是，优先查找本地的参数变量，再在上下文中查找
        fn execute (
            &self, 
            args: Vec<PrimValues>
        ) -> Result<PrimValues, ExecError> {
            let vars_dict: HashMap<Identifier, PrimValues> = self.args.iter().map(|(var, _)| var.clone()).zip(args).collect();
            let f = self.body.execute(|var| {
                if let Some(value) = vars_dict.get(&var) {
                    Ok(Either::<PrimValues, FunctionVar>::Left(*value))    // 用 EmptyFunctionVar，表示这里不会返回函数变量
                } else {
                    if let Ok(Either::<PrimValues, FunctionVar>::Right(f)) = self.context.get_value(var.clone()) {
                        Ok(Either::<PrimValues, FunctionVar>::Right(f.clone()))
                    } else {
                    Err(GetValueError::VarNotDefined(format!("{:?}", var)))
                    }
                }
            });
            f
        }
    }    

    // use super::function::{Function, GetValueError};
    // use super::function::{ExecutableFunction, DefinedFunction, FunctionVar};
    // impl <Var: VarIndex, Terms, Types: Copy> Function<Var, Types> for DefineFun<Var, Terms, Types> {
    //     fn get_args(&self) -> impl Iterator<Item = (Var, Types)> {
    //         self.args.iter().copied()
    //     }
    //     fn get_return_type(&self) -> Types {
    //         self.return_type
    //     }
    //     fn get_name(&self) -> String {
    //         self.name.clone()
    //     }
        
    // }
    // impl <Var: VarIndex, Terms: PositionedExecutable<Var, Types, Terms>, Types: Copy> NamedExecutable<Var, Types, Terms> for DefineFun<Var, Terms, Types> {
    //     fn get_args(&self) -> impl Iterator<Item = (Var, Types)> {
    //         self.args.iter().copied()
    //     }
    //     fn execute<F: FnOnce(Var) -> Result<Terms, GetValueError>> (
    //         &self, 
    //         args_map: F
    //     ) -> Result<Terms, ExecError> {
    //         let args = self.args.iter().map(|(var, _)| args_map(*var)).collect::<Result<Vec<_>, _>>()?;
    //         self.body.execute(args)
    //     }
    // }
}

// pub mod exp {


//     impl <Var: VarIndex, Terms, Types> FunctionVar<Var, Types, Terms> for DefineFun<Var, Terms, Types> {
//         fn get_var_index(&self) -> Var {
//             self.var_index
//         }
//     }
//     impl <Var: VarIndex, Terms, Types> DefinedFunction<Var, Types, Terms> for DefineFun<Var, Terms, Types> {
        
//     }
// }
// pub mod parser {
//     use super::exp::Exp;
//     use either::Either;
//     pub trait Parser<Var, Terms, Types> {
//         fn parse_atom(atom: sexp::Atom) -> Option<Either<Terms, Var>>;
//         fn parse_exp(source: sexp::Sexp) -> Option<Exp<Var, Terms>> {
//             match source {
//                 sexp::Sexp::Atom(atom) => {
//                     match Self::parse_atom(atom) {
//                         Some(Either::Left(value)) => Some(Exp::Value(value)),
//                         Some(Either::Right(var)) => Some(Exp::Var(var)),
//                         None => None
//                     }
//                 },
//                 sexp::Sexp::List(list) => {
//                     let mut iter = list.into_iter();
//                     let head = iter.next()?;
//                     let f = Self::parse_exp(head)?;
//                     let args = iter.map(|x| Self::parse_exp(x)).collect::<Option<Vec<_>>>()?;
//                     Some(Exp::Apply(Box::new(f), args))
//                 }
//             }
//         }
//     } 
// }