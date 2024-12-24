pub mod function {
    use std::{collections::HashMap, sync::Arc};

    use either::Either;
    
    #[derive(Debug)]
    pub enum GetValueError {
        VarNotDefinedWhenGet(String),
        VarNotAssignedWhenGet(String)
    }
    #[derive(Debug)]
    pub enum ExecError {
        VarNotDefinedWhenExec(String),
        VarNotAssignedWhenExec(String),
        TypeMismatch(String),
        DivZero
    }
    /// 无上下文，可按位置执行的函数
    pub trait PositionedExecutable<Var, Terms, ReturnType> {
        /// 如果有参数未赋值，返回 None
        fn execute (
            &self, 
            args: &Vec<Terms>,
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
        fn execute<F: Fn(&Identifier) -> Result<Either<Values, FunctionVar>, GetValueError> + Copy> (
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
    pub enum LogicTag {
        LIA,
        BV 
    }
    impl LogicTag {
        pub fn get_name(&self) -> &'static str {
            match self {
                LogicTag::LIA => "LIA",
                LogicTag::BV => "BV"
            }
        }
    }
    pub fn parse_logic_tag(exp: Atom) -> LogicTag {
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
    use std::borrow::Borrow;
    use std::sync::Arc;
    use std::{collections::HashMap, rc::Rc};
    use std::hash::Hash;
    use std::fmt::Debug;
    use either::Either;

    use super::function::{ExecError, NamedExecutable, GetValueError, PositionedExecutable};
    /// 表示当前函数体内的上下文。
    /// 我们将变量分为两类，已经赋值的和未赋值的。
    pub trait Scope<Identifier: Clone, Types, Values, FunctionVar: PositionedExecutable<Identifier, Values, Values>> {
        /// 获取当前作用域内的所有变量及其类型的迭代器，注意只会返回当前 Scope 内的而不会返回上层 Scope 的变量
        fn get_all_vars(&self) -> impl Iterator<Item = (Identifier, Types)>;

        /// 获取当前作用域内的变量类型，None 表示无这个变量。只能获取非函数变量
        fn get_type(&self, var: &Identifier) -> Option<Types>;

        /// 获取当前作用域内的变量值，优先返回本层的，如果本层没有则返回上层的
        fn get_value(&self, var: &Identifier) -> Result<Either<Values, FunctionVar>, GetValueError>;

        /// 设置当前作用域内的变量值，返回是否设置成功。只能设置本层的非函数变量
        fn set_value(&mut self, var: Identifier, value: Values) -> Option<()>;
        
        /// 设置当前作用域内的函数变量值，返回是否设置成功。只能设置本层的函数变量
        fn set_function_var(&mut self, var: Identifier, value: FunctionVar) -> Option<()>;

        /// 添加新变量，重复添加则会失败
        fn add_var(&mut self, var: Identifier, var_type: Types) -> Option<()>;

        /// 添加新函数变量，重复添加则会失败
        fn add_function_var(&mut self, var: Identifier, var_type: Types) -> Option<()>;

        fn add_and_set_function_var(&mut self, var: Identifier, var_type: Types, value: FunctionVar) -> Option<()> {
            self.add_function_var(var.clone(), var_type)?;
            self.set_function_var(var, value)
        }

        /// 在当前 scope 下执行函数
        fn execute_in<ResultType>(&self, f: impl NamedExecutable<Identifier, Values, FunctionVar, ResultType>) -> Result<ResultType, ExecError> {
            f.execute(|var| self.get_value(var))
        }
        /// 产生新的子作用域
        fn fork(parent: Arc<Self>) -> Self;
    }
    #[derive(Debug, Clone)]
    pub struct ScopeImpl<Identifier, Types, Values, FunctionVar: PositionedExecutable<Identifier, Values, Values>> {
        pub all_vars: HashMap<Identifier, Types>,
        pub non_function_vars: HashMap<Identifier, Values>,
        pub function_vars: HashMap<Identifier, FunctionVar>,
        pub parent_scope: Option<Arc<ScopeImpl<Identifier, Types, Values, FunctionVar>>>,
    }
    impl<
            Identifier: Eq + Hash + Clone + Debug,
            Types: Copy,
            Values: Copy,
            FunctionVar: PositionedExecutable<Identifier, Values, Values> + Clone,
        > ScopeImpl<Identifier, Types, Values, FunctionVar>
    {
        pub fn new(
            parent_scope: Option<Arc<ScopeImpl<Identifier, Types, Values, FunctionVar>>>,
        ) -> Self {
            ScopeImpl {
                all_vars: HashMap::new(),
                non_function_vars: HashMap::new(),
                function_vars: HashMap::new(),
                parent_scope
            }
        }
        pub fn new_empty() -> Self {
            ScopeImpl {
                all_vars: HashMap::new(),
                non_function_vars: HashMap::new(),
                function_vars: HashMap::new(),
                parent_scope: None
            }
        }
        
    }
    impl <Identifier: Eq + Hash + Clone + Debug, Types: Copy, Values: Copy, FunctionVar: PositionedExecutable<Identifier, Values, Values> + Clone> Scope<Identifier, Types, Values, FunctionVar> for ScopeImpl<Identifier, Types, Values, FunctionVar> {
        fn get_all_vars(&self) -> impl Iterator<Item = (Identifier, Types)> {
            self.all_vars.iter().map(|(k, v)| (k.clone(), *v))
        }
        fn get_type(&self, var: &Identifier) -> Option<Types> {
            self.all_vars.get(var).copied()
        }
        fn get_value(&self, var: &Identifier) -> Result<Either<Values, FunctionVar>, GetValueError> {
            if let Some(value) = self.non_function_vars.get(&var) {
                Ok(Either::Left(*value))
            } else if let Some(value) = self.function_vars.get(&var) {
                Ok(Either::Right(value.clone()))
            } else {
                match self.parent_scope {
                    Some(ref parent) => parent.get_value(var),
                    None => Err(GetValueError::VarNotDefinedWhenGet(format!("{:?}", var)))
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
        fn add_var(&mut self, var: Identifier, var_type: Types) -> Option<()> {
            if self.all_vars.contains_key(&var) {
                None
            } else {
                self.all_vars.insert(var, var_type);
                Some(())
            }
        }
        fn add_function_var(&mut self, var: Identifier, var_type: Types) -> Option<()> {
            if self.all_vars.contains_key(&var) {
                None
            } else {
                self.all_vars.insert(var, var_type);
                Some(())
            }
        }
        fn fork(parent: Arc<Self>) -> Self {
            ScopeImpl::new(Some(parent))
        }
    }

}

pub mod language {
    use std::{borrow::Borrow, cell::OnceCell, collections::{HashMap, HashSet}, fmt::{format, Debug}, hash::Hash, marker::PhantomData, rc::Rc, sync::{Arc, OnceLock}, task::Context};

    use either::Either;

    use super::{function::{BuiltinFunction, ExecError, ExplicitParameter, GetValueError, NamedExecutable, PositionedExecutable, VarIndex}, scope::{self, Scope}};

    pub trait Type 
    where Self: Sized
    {
        fn from_identifier(identifier: &str) -> Option<Self>;
        fn from_function(args: Vec<Self>, return_type: Self) -> Self;
    }

    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub enum Terms<Var: Clone + Eq, PrimValues: Copy + Eq> {
        Var(Var),
        PrimValue(PrimValues),
    }


    // 由于本次作业似乎不需要，因此这里 Exp 就不带类型了
    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub enum Exp<Identifier: Clone + Eq, PrimValues: Copy + Eq> {
        Value(Terms<Identifier, PrimValues>),
        Apply(Identifier, Vec<Exp<Identifier, PrimValues>>),   // 注意我们使用的语言中，函数应用中的函数只能是 Identifier
    } 
    


    impl <
        Identifier: VarIndex + Clone + Debug + Eq, 
        PrimValues: Copy + Debug + Eq,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        > 
    NamedExecutable<Identifier, PrimValues, FunctionVar, PrimValues> for Exp<Identifier, PrimValues> {
        /// 注意我们允许零个参数的 FunctionVar
        fn execute<F: Fn(&Identifier) -> Result<Either<PrimValues, FunctionVar>, GetValueError> + Copy> (
            &self, 
            args_map: F
        ) -> Result<PrimValues, ExecError> {
            match self {
                Exp::Value(value) => {
                    match value {
                        Terms::Var(var) => {
                            match args_map(var) {
                                Ok(Either::Left(x)) => Ok(x),
                                Ok(Either::Right(f)) => f.execute(&vec![]),
                                Err(GetValueError::VarNotAssignedWhenGet(s)) => Err(ExecError::VarNotAssignedWhenExec(format!("{:?}, when exec Exp::value", s))),
                                Err(GetValueError::VarNotDefinedWhenGet(s)) => Err(ExecError::VarNotDefinedWhenExec(format!("{:?}, when exec Exp::value", s)))
                        }
                        },
                        Terms::PrimValue(value) => Ok(*value)
                    }
                },
                Exp::Apply(f, args) => {
                    let f = match args_map(f) {
                        Ok(Either::Left(x)) => return Err(ExecError::TypeMismatch(format!("{:?}", x))),
                        Ok(Either::Right(f)) => f,
                        Err(GetValueError::VarNotAssignedWhenGet(s)) => return Err(ExecError::VarNotAssignedWhenExec(format!("{:?}, when exec Exp::Apply({:?}, {:?})", s, f, args))),
                        Err(GetValueError::VarNotDefinedWhenGet(s)) => return Err(ExecError::VarNotDefinedWhenExec(format!("{:?}, when exec Exp::Apply({:?}, {:?})", s, f, args)))
                    };
                    let args = args.iter().map(|x| x.execute(args_map)).collect::<Result<Vec<_>, _>>()?;
                    f.execute(&args)
                }
            }
        }
    }

    /// 注意我们不考虑函数变量的情况
    // fn count_vars_occurrence<
    //     Identifier: Clone + Eq + Hash,
    //     PrimValues: Copy + Eq,
    //     F: Fn(&Identifier) -> bool + Clone
    //     > 
    //     (
    //         exp: &Exp<Identifier, PrimValues>, 
    //         contains: F
    //     ) 
    //     -> HashMap<Identifier, usize> {
    //     match exp {
    //         Exp::Value(Terms::Var(var)) => {
    //             if contains(var) {
    //                 let mut map = HashMap::new();
    //                 map.insert(var.clone(), 1);
    //                 map
    //             } else {
    //                 HashMap::new()
    //             }
    //         },
    //         Exp::Value(Terms::PrimValue(_)) => HashMap::new(),
    //         Exp::Apply(_, args) => {
    //             args.iter().map(|x| count_vars_occurrence(x, contains.clone())).fold(HashMap::new(), |mut acc, x| {
    //                 for (k, v) in x {
    //                     *acc.entry(k).or_insert(0) += v;
    //                 }
    //                 acc
    //             })
    //         }
    //     }
    // }

    pub(crate) fn count_vars_occurrence<
        'a,
        Identifier: Clone + Eq + Hash,
        PrimValues: Copy + Eq,
        F: Fn(&Identifier) -> bool + Clone
        > 
        (
            exp: &'a mut Exp<Identifier, PrimValues>, 
            contains: F
        ) 
        -> HashMap<Identifier, Vec<&'a mut Exp<Identifier, PrimValues>>> {
        match exp {
            Exp::Value(Terms::Var(var)) => {
                if contains(var) {
                    let mut map = HashMap::new();
                    map.entry(var.clone()).or_insert(vec![]).push(exp);
                    return map
                } else {
                    HashMap::new()
                }
            },
            Exp::Value(Terms::PrimValue(_)) => HashMap::new(),
            Exp::Apply(_, args) => {
                args.into_iter().map(|x| count_vars_occurrence(x, contains.clone())).fold(HashMap::new(), |mut acc, x| {
                    for (k, mut v) in x {
                        acc.entry(k).or_insert(vec![]).append(&mut v);
                    }
                    acc
                })
            }
        }
    }

    /// 在给定表达式中，将某个变量的一次出现替换为另一个表达式，返回替换后的表达式
    pub(crate) fn subst_once<Identifier: Clone + Eq, PrimValues: Copy + Eq>(
        exp: Exp<Identifier, PrimValues>,
        var: &Identifier,
        replacement: &Exp<Identifier, PrimValues>,
    ) -> Exp<Identifier, PrimValues> {
        match exp {
            Exp::Value(Terms::Var(v)) => {
                if v == *var {
                    (*replacement).clone()
                } else {
                    Exp::Value(Terms::Var(v))
                }
            },
            Exp::Value(Terms::PrimValue(_)) => exp,
            Exp::Apply(f, args) => {
                Exp::Apply(f.clone(), args.into_iter().map(|x| subst_once(x, var, replacement)).collect())
            }
        }
    }

    /// 最基础的 PositionedExecutable 函数，充当临时变量使用
    pub struct BasicFun<
        Identifier: VarIndex + Clone + Eq, 
        PrimValues: Copy + Eq, 
        Types, 
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues>,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > {
        pub args: Vec<(Identifier, Types)>,
        pub context: Option<Arc<Context>>,
        pub body: Exp<Identifier, PrimValues>,
        _phantom: PhantomData<FunctionVar>
    }

    impl <
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug + Eq, 
        Types,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > BasicFun<Identifier, PrimValues, Types, FunctionVar, Context> {
        pub fn new(
            args: Vec<(Identifier, Types)>,
            context: Option<Arc<Context>>,
            body: Exp<Identifier, PrimValues>
        ) -> Self {
            BasicFun {
                args,
                context,
                body,
                _phantom: PhantomData
            }
        }
    }

    impl <
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug + Eq, 
        Types,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > PositionedExecutable<Identifier, PrimValues, PrimValues> for BasicFun<Identifier, PrimValues, Types, FunctionVar, Context> {
        /// 注意我们的执行规则是，优先查找本地的参数变量，再在上下文中查找
        fn execute (
            &self, 
            args: &Vec<PrimValues>
        ) -> Result<PrimValues, ExecError> {
            let vars_dict: HashMap<Identifier, PrimValues> = self.args.iter().map(|(var, _)| var.clone()).zip(args).map(|(k, v)| (k, *v)).collect();
            let f = self.body.execute(|var| {
                if let Some(value) = vars_dict.get(&var) {
                    Ok(Either::<PrimValues, FunctionVar>::Left(*value))    // 用 EmptyFunctionVar，表示这里不会返回函数变量
                } else {
                    match &self.context {
                        None => Err(GetValueError::VarNotDefinedWhenGet(format!("{:?}", var))),
                        Some(ctx) => ctx.get_value(var)
                    }
                }
            });
            f
        }
    }

    /// 用来声明一个 FunctionVar 可以由一个 BasicFun 生成
    pub trait FromBasicFun<
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug + Eq, 
        Types,
        Context: Scope<Identifier, Types, PrimValues, Self>
    > 
    where Self: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone
    {
        fn from_basic_fun(basic_fun: BasicFun<Identifier, PrimValues, Types, Self, Context>) -> Self;
    }

    #[derive(Debug)]
    pub struct DefineFun<
        Identifier: VarIndex + Clone + Eq, 
        PrimValues: Copy + Eq, 
        Types, 
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues>,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > {
        pub var_index: Identifier,
        pub args: Vec<(Identifier, Types)>,
        pub context: OnceLock<Arc<Context>>,
        pub return_type: Types,
        pub body: Exp<Identifier, PrimValues>,
        pub _phantom: PhantomData<FunctionVar>
    }

    impl <
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug + Eq, 
        Types: Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > DefineFun<Identifier, PrimValues, Types, FunctionVar, Context> {
        pub fn get_name(&self) -> String {
            self.var_index.to_name()
        }
        pub fn to_basic_fun(&self) -> BasicFun<Identifier, PrimValues, Types, FunctionVar, Context> {
            BasicFun::new(self.args.clone(), self.context.get().map(|x| x.clone()), self.body.clone())
        }
    }

    impl <
        'a,
        Identifier: VarIndex + Clone + Eq + Hash + Debug, 
        PrimValues: Copy + Debug + Eq, 
        Types: Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    > 
        PositionedExecutable<Identifier, PrimValues, PrimValues> 
            for DefineFun<Identifier, PrimValues, Types, FunctionVar, Context> {
        /// 注意我们的执行规则是，优先查找本地的参数变量，再在上下文中查找
        fn execute (
            &self, 
            args: &Vec<PrimValues>
        ) -> Result<PrimValues, ExecError> {
            // let vars_dict: HashMap<Identifier, PrimValues> = self.args.iter().map(|(var, _)| var.clone()).zip(args).collect();
            // let f = self.body.execute(|var| {
            //     if let Some(value) = vars_dict.get(&var) {
            //         Ok(Either::<PrimValues, FunctionVar>::Left(*value))    // 用 EmptyFunctionVar，表示这里不会返回函数变量
            //     } else {
            //         if let Some(ref ctx) = self.context.get() {
            //             ctx.get_value(var)
            //         } else {
            //             Err(GetValueError::VarNotDefinedWhenGet(format!("{:?}", var)))
            //         }
            //     }
            // });
            // f
            self.to_basic_fun().execute(args)
        }
    }

    #[derive(Debug, Clone)]
    /// Declare-var
    pub struct DeclareVar<Identifier, Types> {
        var_index: Identifier,
        var_type: Types,
    }

    impl <Identifier, Types> DeclareVar<Identifier, Types> {
        pub fn new(var_index: Identifier, var_type: Types) -> Self {
            DeclareVar {
                var_index,
                var_type
            }
        }
        pub fn get_id(&self) -> &Identifier {
            &self.var_index
        }
        pub fn get_type(&self) -> &Types {
            &self.var_type
        }

    }

    #[derive(Debug, Clone)]
    /// 一条上下文无关文法中的生成规则
    pub struct Rule<Identifier: Clone + Eq, PrimValue: Copy + Eq + Clone> {
        body: Exp<Identifier, PrimValue>,
    } 
    impl <'a, Identifier: Clone + Hash + Eq + Debug, PrimValue: Copy + Eq + Debug> Rule<Identifier, PrimValue> {
        pub fn new(body: Exp<Identifier, PrimValue>) -> Self {
            Rule {
                body,
            }
        }
        /// 将非终结符的每次出现统计成可变引用，需要时直接替换。
        /// 入参用来判定哪些符号是非终结符
        pub fn get_counts<
            F : Fn(&Identifier) -> bool + Clone
        >
        (&'a mut self, contains: F) -> HashMap<Identifier, Vec<&'a mut Exp<Identifier, PrimValue>>> {
            count_vars_occurrence(&mut self.body, contains)
        }
        /// 由于信息不足，这里不会检查是否是非终结符，请在调用前确保是非终结符
        /// 同时，每次调用该函数都会搜索一边表达式树，因此高频率的替换建议使用 get_counts 给出的可变引用
        pub fn subst_non_terminal_once(&self, exp: Exp<Identifier, PrimValue>, var: &Identifier, replacement: &Exp<Identifier, PrimValue>) -> Exp<Identifier, PrimValue> {
            subst_once(exp, var, replacement)
        }

        pub fn get_body(&self) -> &Exp<Identifier, PrimValue> {
            &self.body
        }
    }

    #[derive(Debug, Clone)]
    /// 注意由于 Rule 中 count 的设计，SynthFun 一旦 init_counts 后就无法移动了，需要谨慎使用
    pub struct SynthFun<Identifier: Clone + Eq, PrimValue: Copy + Eq, Types> {
        /// 函数名
        name: Identifier,
        /// 参数列表
        args: Vec<(Identifier, Types)>,
        /// 返回值类型
        return_type: Types,
        /// 每个非终结符对应的生成规则
        rules: HashMap<Identifier, Vec<Rule<Identifier, PrimValue>>>,
        /// 每个非终结符对应的类型
        types_of_non_terminal: HashMap<Identifier, Types>,
    }

    impl <Identifier: Clone + Eq + Hash + Debug, PrimValue: Copy + Eq + Debug, Types> SynthFun<Identifier, PrimValue, Types> {
        pub fn new(
            name: Identifier,
            args: Vec<(Identifier, Types)>,
            return_type: Types,
            rules: HashMap<Identifier, Vec<Rule<Identifier, PrimValue>>>,
            types_of_non_terminal: HashMap<Identifier, Types>,
        ) -> Self {
            SynthFun {
                name,
                args,
                return_type,
                rules,
                types_of_non_terminal,
            }
        }
        // 由于修改了实现，下面的方法有点没有意义，请在使用时手动获取每个 Rule 的非终结符引用  
        // pub fn get_all_counts(&mut self) {
        //     for rules in self.rules.values_mut() {
        //         for rule in rules {
        //             rule.get_counts(|var| self.types_of_non_terminal.contains_key(var));
        //         }
        //     }
        // }
        pub fn get_name(&self) -> &Identifier {
            &self.name
        }
        pub fn get_args(&self) -> &Vec<(Identifier, Types)> {
            &self.args
        }
        pub fn get_return_type(&self) -> &Types {
            &self.return_type
        }
        // 为了安全起见，这里不提供 Rule 的可变引用。使用时，可以将每个 Rule 复制一次，在复制的 Rule 上进行操作
        pub fn get_rules(&self, non_terminal: &Identifier) -> Option<&Vec<Rule<Identifier, PrimValue>>> {
            self.rules.get(non_terminal)
        }
        pub fn get_type(&self, non_terminal: &Identifier) -> Option<&Types> {
            self.types_of_non_terminal.get(non_terminal)
        }
        pub fn get_non_terminal_checker(&self) -> (impl Fn(&Identifier) -> bool + Clone + use<'_, Identifier, PrimValue, Types>) {
            |var| self.types_of_non_terminal.contains_key(var)
        }

        /// 得到当前 这个 id 是否是终结符
        pub fn is_terminal(&self, id: &Identifier) -> bool {
            self.types_of_non_terminal.get(id).is_none()
        }
        
        /// 得到当前 rules 中的所有产生式中的表达式
        pub fn get_all_exp(&self) -> Vec<Exp<Identifier, PrimValue>> {
            self.rules.keys().flat_map(|id| self.rules.get(id).unwrap().iter().map(|rule| rule.get_body().clone())).collect()
        }

        pub fn get_all_rules_with_non_terminals(&self) -> &HashMap<Identifier, Vec<Rule<Identifier, PrimValue>>> {
            &self.rules
        }

        pub fn get_all_rules(&self) -> &HashMap<Identifier, Vec<Rule<Identifier, PrimValue>>> {
            &self.rules
        }

    }
    impl <
        Identifier: Clone + Eq + Hash + VarIndex + Debug, 
        PrimValue: Copy + Eq + Debug, 
        Types: Clone,
    > SynthFun<Identifier, PrimValue, Types> {
        /// 将指定的 exp 视作当前 SynthFun 的 body 并返回一个（临时的） BasicFun
        pub fn exp_to_basic_fun<
            FunctionVar: PositionedExecutable<Identifier, PrimValue, PrimValue> + Clone,
            Context: Scope<Identifier, Types, PrimValue, FunctionVar>
        >(
            &self,
            context: Option<Arc<Context>>,
            exp: &Exp<Identifier, PrimValue>
        ) -> BasicFun<Identifier, PrimValue, Types, FunctionVar, Context> {
            BasicFun::new(self.args.clone(), context, exp.clone())
        }

        /// 将指定的 exp 视作当前 SynthFun 的 body 并在给定的信息下执行
        pub fn execute_exp_in_context<
            FunctionVar: PositionedExecutable<Identifier, PrimValue, PrimValue> + Clone,
            Context: Scope<Identifier, Types, PrimValue, FunctionVar>
        >(
            &self,
            args: &Vec<PrimValue>,
            context: Option<Arc<Context>>,
            exp: &Exp<Identifier, PrimValue>
        ) -> Result<PrimValue, ExecError>
        {
            let temp_fun = self.exp_to_basic_fun(context, exp);
            temp_fun.execute(&args)
        }
    }

    pub trait ConstraintPassesValue {
        /// 标明该结果值是否说明约束通过
        fn is_pass(&self) -> bool;
    }

    impl <
        PrimValues: ConstraintPassesValue,
        ExecError
    > ConstraintPassesValue for Result<PrimValues, ExecError> {
        fn is_pass(&self) -> bool {
            match self {
                Ok(v) => {
                    v.is_pass()
                }
                Err(_) => {
                    false
                }
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct Constraint<Identifier: Clone + Eq, PrimValue: Copy + Eq> {
        body: Exp<Identifier, PrimValue>,
    }
    impl <Identifier: Clone + Eq, PrimValue: Copy + Eq> Constraint<Identifier, PrimValue> {
        pub fn new(body: Exp<Identifier, PrimValue>) -> Self {
            Constraint {
                body
            }
        }
        pub fn get_body(&self) -> &Exp<Identifier, PrimValue> {
            &self.body
        }
    }
    impl <Identifier: Clone + Eq + Debug + VarIndex + Hash, PrimValue: Copy + Eq + Debug> Exp<Identifier, PrimValue> {
        /// 在指定的上下文中执行该表达式，优先使用 args_map 中的变量
        pub fn execute_in_optional_context<
            Types,   
            FunctionVar: PositionedExecutable<Identifier, PrimValue, PrimValue> + Clone + FromBasicFun<Identifier, PrimValue, Types, Context>,
            Context: Scope<Identifier, Types, PrimValue, FunctionVar>,
        >(
            &self,
            context: Option<&Context>,
            args_map: impl Fn(&Identifier) -> Result<Either<PrimValue, FunctionVar>, GetValueError> + Copy
        ) -> Result<PrimValue, ExecError>
        {
            self.execute(|var| {
                if let Ok(r) = args_map(var) {
                    Ok(r)
                } else {
                    if let Some(ctx) = context {
                        ctx.get_value(var)
                    } else {
                        // panic!("No context provided");
                        Err(GetValueError::VarNotDefinedWhenGet(format!("{:?}", var)))
                    }
                }
            }
            )
        }
    
        /// 用一个 exp 替代 SynthFun 的对象并在给定的上下文中执行该表达式，其实实现有一点低效，没必要让 FunctionVar 建立一个新的 Rc，但是为了简化代码，这里就这样写了
        pub fn instantiate_and_execute<
            'a,
            Types: Clone,   
            FunctionVar: PositionedExecutable<Identifier, PrimValue, PrimValue> + Clone + FromBasicFun<Identifier, PrimValue, Types, Context>,
            Context: Scope<Identifier, Types, PrimValue, FunctionVar>,
        >(
            &self,
            fun_to_synth: &'a SynthFun<Identifier, PrimValue, Types>,
            context: Option<Arc<Context>>,
            exp: &'a Exp<Identifier, PrimValue>,
            args_map: impl Fn(&Identifier) -> Result<Either<PrimValue, FunctionVar>, GetValueError> + Copy,
        ) -> Result<PrimValue, ExecError>
        {
            let new_args_map = |var: &Identifier| {
                let ctx = context.clone();
                if fun_to_synth.get_name() == var {
                    let temp_func = fun_to_synth.exp_to_basic_fun(ctx.clone(), exp);
                    Ok(Either::Right(FunctionVar::from_basic_fun(temp_func)))
                } else {
                    args_map(var)
                }
            };
            match &context {
                None => self.execute_in_optional_context(None, new_args_map),
                Some(ctx) =>
                    self.execute_in_optional_context(Some(ctx.borrow()), new_args_map)
            }
        }
    }

}