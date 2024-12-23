use std::sync::Arc;
use std::{collections::HashMap, fmt::Debug, hash::Hash, result::Result};

use either::Either::{self, Left, Right};
use z3::{self, ast::Ast};
use z3::{Context, RecFuncDecl, Sort, SortKind};

use z3::ast::{Bool, Dynamic, BV};

use crate::base::language::{BasicFun, Exp, Terms, Type};
use crate::base::{
    function::{PositionedExecutable, VarIndex},
    language::{Constraint, DeclareVar, DefineFun, SynthFun},
    scope::Scope,
};
use crate::lia_logic::lia::{self};

pub trait GetZ3Type<'ctx> {
    fn get_z3_type(&self, context: &'ctx Context) -> z3::Sort<'ctx>;
}

pub trait GetZ3Assert<'ctx, Identifier: VarIndex + Clone + Eq + Hash, 
PrimValues: Copy + Eq + Debug + GetZ3Value<'ctx> + NewPrimValues> {
    /// 把一个 Assertion 转换为 Z3 的表达式
    fn get_z3_assert(
        &self,
        context: &'ctx Context,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> z3::ast::Bool<'ctx>;
}

pub trait GetZ3Value<'ctx> {
    /// 把一个值转换为 Z3 的值
    fn get_z3_value(&self, context: &'ctx Context) -> Dynamic<'ctx>;
}

pub trait GetZ3Decl<'ctx, Identifier: VarIndex + Clone + Eq + Hash, 
PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues> {
    /// 对于 DefineFun 来说，返回的是一个 RecFuncDecl + 它的定义
    fn get_z3_decl(
        &self,
        ctx: &'ctx z3::Context,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> z3::RecFuncDecl<'ctx>;
}

pub trait GetZ3Var<'ctx, Identifier: VarIndex + Clone + Eq + Hash,
PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues> {
    /// 把一个变量转换为 Z3 的变量
    fn get_z3_var(
        &self,
        ctx: &'ctx z3::Context,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx>;
}

pub trait GetZ3Expr<'ctx, Identifier: VarIndex + Clone + Eq + Hash,
PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues> {
    /// 对于一个 Exp 转换为 Z3 表达式
    fn get_z3_expr(
        &self,
        ctx: &'ctx z3::Context,
        args: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx>;
}

pub trait GetZ3DeclExpr<'ctx, Identifier: VarIndex + Clone + Eq + Hash, 
PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues> {
    /// 对于一个 Exp 转换为 Z3 表达式
    fn get_z3_decl_expr(
        &self,
        ctx: &'ctx z3::Context,
        args: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx>;
}

pub trait GetPrimValue<'ctx, PrimValues: GetZ3Value<'ctx> + Copy + Eq> {
    fn get_prim_value(&self) -> PrimValues;
}

pub trait NewPrimValues {
    fn new(z3_val: &Dynamic) -> Self;
}

pub trait Z3SortToTypes<Types: Type> {
    fn to_types(&self) -> Types;
}

/// Z3Solver 是一个封装了 Z3 的求解器的结构体
pub struct Z3Solver<'ctx, Identifier: VarIndex + Clone + Eq + Hash,
    PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues,
> {
    ctx: &'ctx Context,
    solver: z3::Solver<'ctx>,
    synth_fun: Option<z3::RecFuncDecl<'ctx>>,
    defined_funs: HashMap<Identifier, z3::RecFuncDecl<'ctx>>,
    declared_vars: HashMap<Identifier, z3::ast::Dynamic<'ctx>>,
    constraints: &'ctx [Constraint<Identifier, PrimValues>],
}

// TODO: 要把Context里面的 builtin 的函数也加入进来
impl<'ctx, Identifier: VarIndex + Clone + Eq + Hash + Debug,
    PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues,
> Z3Solver<'ctx, Identifier, PrimValues> {
    /// 创建一个新的 Z3Solver
    /// 里面已经包含了所有的约束, 但是约束里的 f 是未知的
    /// 你需要传入一个 'ctx 的 Z3 Context
    pub fn new<
        Types: GetZ3Type<'ctx> + Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    >(
        define_funs: &[Arc<DefineFun<Identifier, PrimValues, Types, FunctionVar, Context>>],
        declare_vars: &[DeclareVar<Identifier, Types>],
        synth_fun: &SynthFun<Identifier, PrimValues, Types>,
        constraints: &'ctx [Constraint<Identifier, PrimValues>],
        ctx: &'ctx z3::Context,
    ) -> Self {
        let mut z3_solver: Z3Solver<'ctx, Identifier, PrimValues> = Z3Solver {
            ctx: ctx,
            solver: z3::Solver::new(ctx),
            synth_fun: None,
            defined_funs: HashMap::new(),
            declared_vars: HashMap::new(),
            constraints,
        };

        // 我只需要先建立一个 Decl 就好了
        let synth_fun_decl = synth_fun.get_z3_decl(&ctx, &z3_solver);
        z3_solver.synth_fun = Some(synth_fun_decl);

        for defined_fun in define_funs {
            let decl = defined_fun.get_z3_decl(&ctx, &z3_solver);
            z3_solver
                .defined_funs
                .insert(defined_fun.var_index.clone(), decl);
        }

        for declare_var in declare_vars {
            let z3_decl = declare_var.get_z3_var(&ctx, &z3_solver);
            z3_solver
                .declared_vars
                .insert(declare_var.get_id().clone(), z3_decl);
        }

        z3_solver
    }

    /// 传递进来一个已经填充好的 SynthFun，返回一个 SAT or CounterExample
    /// 应该传递进来的是一个 BasicFun
    /// 返回作为反例的所有输入, 以及不满足的规约
    pub fn get_counterexample<
        Types: GetZ3Type<'ctx> + Clone + Type,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    >(
        &mut self,
        synth_fun: &BasicFun<Identifier, PrimValues, Types, FunctionVar, Context>,
    ) -> Result<
        Either<
            HashMap<Identifier, (Types, PrimValues)>,
            String,
        >,
        String
    > {
        self.solver.reset();
        let args = synth_fun
            .args
            .iter()
            .map(|(id, ty)| {
                let z3_decl = get_z3_decl_with_type(self.ctx, id.clone(), ty.clone());
                z3_decl
            })
            .collect::<Vec<_>>();
        let args_ref = args.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
        let args_hashmap: HashMap<Identifier, &dyn Ast<'ctx>> = synth_fun
            .args
            .iter()
            .zip(args_ref.iter()) // Combine the self_args and args
            .map(|((id, _ty), arg)| (id.clone(), *arg)) // Create (Identifier, &dyn Ast<'ctx>)
            .collect();

        let synth_fun_expr = synth_fun.get_z3_decl_expr(self.ctx, &args_hashmap, self);
        self.synth_fun.as_ref().unwrap().add_def(args_ref.as_slice(), &synth_fun_expr);
        let mut assert = Bool::from_bool(self.ctx, true);
        for constraint in self.constraints {
            let z3_constraint = constraint.get_z3_assert(&self.ctx, &self);
            assert = Bool::and(&self.ctx, &[&assert, &z3_constraint]);
        }
        self.solver.assert(&assert.not());

        let res = self.solver.check();
        match res {
            z3::SatResult::Unsat => {
                return Ok(Right("Synth Function Passed All Constraints".to_string()));
            }
            z3::SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut result = HashMap::new();
                for (id, z3_var) in &self.declared_vars {
                    let z3_value = model.eval(z3_var, true).unwrap();
                    let value = z3_value.get_prim_value();
                    let ty: Types = z3_var.get_sort().to_types();
                    result.insert(id.clone(), (ty.clone(), value));
                }
                return Ok(Left(result));
            }
            _ => {
                return Err("Solver Unknown".to_string());
            }
        }
    }
    /// 得到一个函数的定义, 是一个引用
    pub fn get_func_decl(&self, id: &Identifier) -> &z3::RecFuncDecl<'ctx> {
        let func = self.defined_funs.get(id);
        match func {
            Some(f) => f,
            None => {
                if self.synth_fun.as_ref().unwrap().name().to_string() == id.to_name() {
                    return self.synth_fun.as_ref().unwrap();
                } else {
                    panic!("Function not found in defined_funs");
                }
            }
        }
    }

    pub fn get_solver(&self) -> &z3::Solver<'ctx> {
        &self.solver
    }

    pub fn get_synth_fun(&self) -> &z3::RecFuncDecl<'ctx> {
        self.synth_fun.as_ref().unwrap()
    }

    pub fn get_defined_funs(&self) -> &HashMap<Identifier, z3::RecFuncDecl<'ctx>> {
        &self.defined_funs
    }
}

impl<'ctx, PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues>
    GetPrimValue<'ctx, PrimValues> for z3::ast::Dynamic<'ctx>
{
    fn get_prim_value(&self) -> PrimValues {
        PrimValues::new(&self)
    }
}

pub fn get_z3_decl_with_type<
    'ctx,
    Identifier: VarIndex + Clone + Eq + Hash,
    Types: GetZ3Type<'ctx>,
>(
    ctx: &'ctx z3::Context,
    id: Identifier,
    ty: Types,
) -> z3::ast::Dynamic<'ctx> {
    let z3_ty = ty.get_z3_type(ctx);
    let z3_decl: Dynamic<'ctx> = match z3_ty.kind() {
        SortKind::Int => z3::ast::Int::new_const(ctx, id.to_name()).into(),
        SortKind::Bool => z3::ast::Bool::new_const(ctx, id.to_name()).into(),
        _ => panic!("Unsupported Type"),
    };
    z3_decl
}

impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
    > GetZ3Expr<'ctx, Identifier, PrimValues> for Exp<Identifier, PrimValues>
{
    /// 暂时先不要考虑会用到前面定义的变量的情况
    fn get_z3_expr(
        &self,
        ctx: &'ctx z3::Context,
        args_map: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier,PrimValues>,
    ) -> Dynamic<'ctx> {
        match self {
            Exp::Value(val) => match val {
                Terms::PrimValue(pv) => {
                    return pv.get_z3_value(ctx);
                }
                Terms::Var(v) => {
                    let var = z3_solver.declared_vars.get(v);
                    match var {
                        Some(v) => {
                            return Dynamic::from_ast(v);
                        }
                        None => {
                            panic!("Variable not found in args_map");
                        }
                    }
                }
            },
            Exp::Apply(f, args) => {
                let z3_args: Vec<Dynamic> = args
                    .iter()
                    .map(|x| x.get_z3_expr(ctx, args_map, z3_solver))
                    .collect();

                let is_builtin = check_z3_builtin(&z3_args, f.to_name().as_str());
                match is_builtin {
                    Ok(res) => {
                        return res;
                    }
                    Err(_) => {}
                }

                let z3_args_ref = z3_args.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
                let z3_args_array = z3_args_ref.as_slice();
                let func = z3_solver.get_func_decl(f);
                let now_func = func.apply(z3_args_array);
                now_func
            }
        }
    }
}

impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
    > GetZ3DeclExpr<'ctx, Identifier, PrimValues> for Exp<Identifier, PrimValues>
{
    /// 暂时先不要考虑会用到前面定义的变量的情况
    fn get_z3_decl_expr(
        &self,
        ctx: &'ctx z3::Context,
        args_map: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx> {
        match self {
            Exp::Value(val) => match val {
                Terms::PrimValue(pv) => {
                    return pv.get_z3_value(ctx);
                }
                Terms::Var(v) => {
                    let var = args_map.get(v);
                    match var {
                        Some(v) => {
                            return Dynamic::from_ast(*v);
                        }
                        None => {
                            panic!("Variable not found in args_map");
                        }
                    }
                }
            },
            Exp::Apply(f, args) => {
                let z3_args: Vec<Dynamic> = args
                    .iter()
                    .map(|x| x.get_z3_decl_expr(ctx, args_map, z3_solver))
                    .collect();
                let is_builtin = check_z3_builtin(&z3_args, f.to_name().as_str());
                match is_builtin {
                    Ok(res) => {
                        return res;
                    }
                    Err(_) => {}
                }

                let z3_args_ref = z3_args.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
                let z3_args_array = z3_args_ref.as_slice();
                let func = z3_solver.get_func_decl(f);
                let now_func = func.apply(z3_args_array);
                now_func
            }
        }
    }
}

/// 实现 BasicFun 的转换为 Z3 的 Expr
impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
        Types,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues>,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    > GetZ3Expr<'ctx, Identifier, PrimValues>
    for BasicFun<'_, Identifier, PrimValues, Types, FunctionVar, Context>
{
    fn get_z3_expr(
        &self,
        ctx: &'ctx z3::Context,
        args_map: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx> {
        self.body.get_z3_expr(ctx, args_map, z3_solver)
    }
}

impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
        Types,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues>,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    > GetZ3DeclExpr<'ctx, Identifier, PrimValues>
    for BasicFun<'_, Identifier, PrimValues, Types, FunctionVar, Context>
{
    fn get_z3_decl_expr(
        &self,
        ctx: &'ctx z3::Context,
        args_map: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx> {
        self.body.get_z3_decl_expr(ctx, args_map, z3_solver)
    }
}

impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
        Types: GetZ3Type<'ctx> + Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    > GetZ3Decl<'ctx, Identifier, PrimValues>
    for DefineFun<Identifier, PrimValues, Types, FunctionVar, Context>
{
    fn get_z3_decl(
        &self,
        ctx: &'ctx z3::Context,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> z3::RecFuncDecl<'ctx> {
        let args_sort: Vec<Sort<'ctx>> = self
            .args
            .iter()
            .map(|(_, ty)| ty.get_z3_type(ctx))
            .collect();
        let args_sort_ref = args_sort.iter().collect::<Vec<_>>();
        let args_sort_array = args_sort_ref.as_slice();

        let args: Vec<Dynamic<'ctx>> = self
            .args
            .iter()
            .map(|(id, ty)| get_z3_decl_with_type(ctx, id.clone(), ty.clone()))
            .collect();
        let args_ref = args.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
        let args_hashmap: HashMap<Identifier, &dyn Ast<'ctx>> = self
            .args
            .iter()
            .zip(args.iter()) // Combine the self_args and args
            .map(|((id, _ty), arg)| (id.clone(), arg as &dyn Ast<'ctx>)) // Create (Identifier, &dyn Ast<'ctx>)
            .collect();
        let args_array = args_ref.as_slice();

        let f = z3::RecFuncDecl::new(
            ctx,
            self.get_name(),
            args_sort_array,
            &self.return_type.get_z3_type(&ctx),
        );

        f.add_def(
            args_array,
            &self.body.get_z3_decl_expr(ctx, &args_hashmap, z3_solver),
        );
        f
    }
}

/// 把 DeclareVar 转换为 Z3 的变量
impl<'ctx, Identifier: VarIndex + Clone + Eq + Hash + Debug, Types: GetZ3Type<'ctx> + Clone,
    PrimValues: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
>
    GetZ3Var<'ctx, Identifier, PrimValues> for DeclareVar<Identifier, Types>
{
    fn get_z3_var(
        &self,
        ctx: &'ctx z3::Context,
        _z3_solver: &Z3Solver<'ctx, Identifier, PrimValues>,
    ) -> Dynamic<'ctx> {
        let ty = self.get_type().get_z3_type(ctx);
        match ty.kind() {
            SortKind::Int => {
                let var = z3::ast::Int::new_const(ctx, self.get_id().to_name());
                Dynamic::from_ast(&var)
            }
            SortKind::Bool => {
                let var = z3::ast::Bool::new_const(ctx, self.get_id().to_name());
                Dynamic::from_ast(&var)
            }
            _ => panic!("Unsupported type"),
        }
    }
}

/// 只是为了得到一个 RecFuncDecl
/// 并不包含 add_def 的操作
impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValue: Copy + Eq + Debug + GetZ3Value<'ctx> + NewPrimValues,
        Types: GetZ3Type<'ctx>,
    > GetZ3Decl<'ctx, Identifier, PrimValue> for SynthFun<Identifier, PrimValue, Types>
{
    fn get_z3_decl(
        &self,
        context: &'ctx z3::Context,
        _z3_solver: &Z3Solver<'ctx, Identifier, PrimValue>,
    ) -> RecFuncDecl<'ctx> {
        let arg_sorts = self
            .get_args()
            .iter()
            .map(|(_, ty)| ty.get_z3_type(context))
            .collect::<Vec<_>>();
        let args_sort_ref = arg_sorts.iter().collect::<Vec<_>>();
        let args_sort_array = args_sort_ref.as_slice();
        let sort = self.get_return_type().get_z3_type(context);
        let func = RecFuncDecl::new(context, self.get_name().to_name(), args_sort_array, &sort);
        func
    }
}

impl<
        'ctx,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValue: Copy + Debug + Eq + GetZ3Value<'ctx> + NewPrimValues,
    > GetZ3Assert<'ctx, Identifier, PrimValue> for Constraint<Identifier, PrimValue>
{
    fn get_z3_assert(
        &self,
        ctx: &'ctx z3::Context,
        z3_solver: &Z3Solver<'ctx, Identifier, PrimValue>,
    ) -> z3::ast::Bool<'ctx> {
        let assert = self
            .get_body()
            .get_z3_expr(ctx, &HashMap::new(), z3_solver)
            .as_bool();
        match assert {
            Some(pred) => pred,
            None => panic!("Constraint should be a boolean expression"),
        }
    }
}

impl<'ctx> GetZ3Type<'ctx> for lia::Types {
    fn get_z3_type(&self, ctx: &'ctx z3::Context) -> z3::Sort<'ctx> {
        match self {
            lia::Types::Int => z3::Sort::int(ctx),
            lia::Types::Bool => z3::Sort::bool(ctx),
            lia::Types::Function => panic!("Function type is not supported"),
        }
    }
}

impl<'ctx> GetZ3Value<'ctx> for lia::Values {
    fn get_z3_value(&self, ctx: &'ctx z3::Context) -> z3::ast::Dynamic<'ctx> {
        match self {
            lia::Values::Int(i) => {
                let i = z3::ast::Int::from_i64(ctx, *i);
                i.into()
            }
            lia::Values::Bool(b) => {
                let b = z3::ast::Bool::from_bool(ctx, *b);
                b.into()
            }
        }
    }
}

impl NewPrimValues for lia::Values {
    fn new(z3_val: &Dynamic) -> Self {
        match z3_val.get_sort().kind() {
            z3::SortKind::Int => lia::Values::Int(
                z3_val
                    .as_int()
                    .unwrap()
                    .as_i64()
                    .expect("Expected an integer"),
            ),
            z3::SortKind::Bool => lia::Values::Bool(
                z3_val
                    .as_bool()
                    .unwrap()
                    .as_bool()
                    .expect("Expected a boolean"),
            ),
            _ => panic!("Unsupported sort kind"),
        }
    }
}

impl<Types: Type> Z3SortToTypes<Types> for z3::Sort<'_> {
    fn to_types(&self) -> Types {
        match self.kind() {
            z3::SortKind::Int => Types::from_identifier("Int").unwrap(),
            z3::SortKind::Bool => Types::from_identifier("Bool").unwrap(),
            _ => panic!("Unsupported sort kind"),
        }
    }
}

/// 检查当前是否是一个 Z3 的内建函数
fn check_z3_builtin<'ctx>(
    args: &Vec<Dynamic<'ctx>>,
    f: &str,
) -> Result<Dynamic<'ctx>, String> {
    match f {
        "=" => {
            arg_num_check(args, 2, "=");
            Ok(args[0]._eq(&args[1]).into())
        }
        "+" => {
            arg_num_check(args, 2, "+");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap() + args[1].as_int().unwrap()).into()),
                SortKind::BV => Ok((args[0].as_bv().unwrap() + args[1].as_bv().unwrap()).into()),
                _ => Err(format!("Unsupported type in +: {:?}", kind)),
            }
        }
        "-" => {
            arg_num_check(args, 2, "-");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap() - args[1].as_int().unwrap()).into()),
                SortKind::BV => Ok((args[0].as_bv().unwrap() - args[1].as_bv().unwrap()).into()),
                _ => Err(format!("Unsupported type in -: {:?}", kind)),
            }
        }
        "*" => {
            arg_num_check(args, 2, "*");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap() * args[1].as_int().unwrap()).into()),
                SortKind::BV => Ok((args[0].as_bv().unwrap() * args[1].as_bv().unwrap()).into()),
                _ => Err(format!("Unsupported type in *: {:?}", kind)),
            }
        }
        "mod" => {
            arg_num_check(args, 2, "mod");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap() % args[1].as_int().unwrap()).into()),
                SortKind::BV => Ok((args[0].as_bv().unwrap().bvsmod(&args[1].as_bv().unwrap())).into()),
                _ => Err(format!("Unsupported type in mod: {:?}", kind)),
            }
        }
        "<" => {
            arg_num_check(args, 2, "<");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap().lt(&args[1].as_int().unwrap())).into()),
                _ => Err(format!("Unsupported type in <: {:?}", kind)),
            }
        }
        ">" => {
            arg_num_check(args, 2, ">");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap().gt(&args[1].as_int().unwrap())).into()),
                _ => Err(format!("Unsupported type in >: {:?}", kind)),
            }
        }
        "<=" => {
            arg_num_check(args, 2, "<=");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap().le(&args[1].as_int().unwrap())).into()),
                _ => Err(format!("Unsupported type in <=: {:?}", kind)),
            }
        }
        ">=" => {
            arg_num_check(args, 2, ">=");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap().ge(&args[1].as_int().unwrap())).into()),
                _ => Err(format!("Unsupported type in >=: {:?}", kind)),
            }
        }
        "and" => {
            arg_num_check(args, 2, "and");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Bool => Ok((args[0].as_bool().unwrap() & args[1].as_bool().unwrap()).into()),
                _ => Err(format!("Unsupported type in and: {:?}", kind)),
            }
        }
        "or" => {
            arg_num_check(args, 2, "or");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Bool => Ok((args[0].as_bool().unwrap() | args[1].as_bool().unwrap()).into()),
                _ => Err(format!("Unsupported type in or: {:?}", kind)),
            }
        }
        "not" => {
            arg_num_check(args, 1, "not");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Bool => Ok(args[0].as_bool().unwrap().not().into()),
                _ => Err(format!("Unsupported type in not: {:?}", kind)),
            }
        }
        "ite" => {
            arg_num_check(args, 3, "ite");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::Bool {
                return Err(format!("Expected Bool in ite, got {:?}", kind));
            }
            Ok(Bool::ite(&args[0].as_bool().unwrap(), &args[1], &args[2]).into())
        }
        _ => Err(format!("Unsupported function: {}", f)),
    }
}


fn arg_num_check<'ctx>(args: &Vec<Dynamic<'ctx>>, num: usize, func_name: &str) {
    if args.len() != num {
        panic!("Expected {} arguments in {}, got {}", num, func_name, args.len());
    }

    match func_name {
        "=" => {
            let arg1_kind = args[0].get_sort().kind();
            let arg2_kind = args[1].get_sort().kind();
            if arg1_kind != arg2_kind {
                panic!("Expected same type in =, got {:?} and {:?}", arg1_kind, arg2_kind);
            }
        }
        "+" | "-" | "*" | "mod" => {
            let arg1_kind = args[0].get_sort().kind();
            let arg2_kind = args[1].get_sort().kind();
            if arg1_kind != arg2_kind {
                panic!("Expected same type in {}, got {:?} and {:?}", func_name, arg1_kind, arg2_kind);
            }
            if arg1_kind != SortKind::Int && arg1_kind != SortKind::BV {
                panic!("Expected Int or BV in {}, got {:?}", func_name, arg1_kind);
            }
        }
        "<" | ">" | "<=" | ">=" => {
            let arg1_kind = args[0].get_sort().kind();
            let arg2_kind = args[1].get_sort().kind();
            if arg1_kind != arg2_kind {
                panic!("Expected same type in {}, got {:?} and {:?}", func_name, arg1_kind, arg2_kind);
            }
            if arg1_kind != SortKind::Int {
                panic!("Expected Int in {}, got {:?}", func_name, arg1_kind);
            }
        }
        "and" | "or" => {
            for arg in args {
                let arg_kind = arg.get_sort().kind();
                if arg_kind != SortKind::Bool {
                    panic!("Expected Bool in {}, got {:?}", func_name, arg_kind);
                }
            }
        }
        "not" => {
            let arg_kind = args[0].get_sort().kind();
            if arg_kind != SortKind::Bool {
                panic!("Expected Bool in {}, got {:?}", func_name, arg_kind);
            }
        }
        "ite" => {
            let arg1_kind = args[0].get_sort().kind();
            if arg1_kind != SortKind::Bool {
                panic!("Expected Bool in {}, got {:?}", func_name, arg1_kind);
            }
            let arg2_kind = args[1].get_sort().kind();
            let arg3_kind = args[2].get_sort().kind();
            if arg2_kind != arg3_kind {
                panic!("Expected same type in {}, got {:?} and {:?}", func_name, arg2_kind, arg3_kind);
            }
        }
        _ => {}
    }
}