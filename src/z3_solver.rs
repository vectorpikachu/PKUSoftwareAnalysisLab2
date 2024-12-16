use std::{collections::HashMap, fmt::Debug, hash::Hash, result::Result};

use z3::{self, ast::Ast};
use z3::{Context, Sort, SortKind};

use z3::ast::Dynamic;

use crate::base::language::BasicFun;
use crate::base::{
    function::{PositionedExecutable, VarIndex},
    language::{Constraint, DeclareVar, DefineFun, SynthFun},
    scope::Scope,
};

pub trait GetZ3Type<'ctx> {
    fn get_z3_type(&self, context: &'ctx Context) -> z3::Sort<'ctx>;
}

pub trait GetZ3Assert<'ctx, Identifier: VarIndex + Clone + Eq + Hash> {
    /// 把一个 Assertion 转换为 Z3 的表达式
    fn get_z3_assert(&self, context: &'ctx Context, z3_solver: &Z3Solver<'ctx, Identifier>) -> z3::ast::Bool<'ctx>;
}

pub trait GetZ3Value<'ctx> {
    /// 把一个值转换为 Z3 的值
    fn get_z3_value(&self, context: &'ctx Context) -> Dynamic<'ctx>;
}

pub trait GetZ3Decl<'ctx, Identifier: VarIndex + Clone + Eq + Hash> {
    /// 对于 DefineFun 来说，返回的是一个 RecFuncDecl + 它的定义
    fn get_z3_decl(
        &self,
        ctx: &'ctx z3::Context,
        z3_solver: &Z3Solver<'ctx, Identifier>,
    ) -> z3::RecFuncDecl<'ctx>;
}

pub trait GetZ3Var<'ctx, Identifier: VarIndex + Clone + Eq + Hash> {
    /// 把一个变量转换为 Z3 的变量
    fn get_z3_var(&self, ctx: &'ctx z3::Context, z3_solver: &Z3Solver<'ctx, Identifier>) -> Dynamic<'ctx>;
}

pub trait GetZ3Expr<'ctx, Identifier: VarIndex + Clone + Eq + Hash> {
    /// 对于一个 Exp 转换为 Z3 表达式
    fn get_z3_expr(
        &self,
        ctx: &'ctx z3::Context,
        args: &HashMap<Identifier, &dyn Ast<'ctx>>,
        z3_solver: &Z3Solver<'ctx, Identifier>,
    ) -> Dynamic<'ctx>;
}

pub trait GetPrimValue<'ctx, PrimValues: GetZ3Value<'ctx> + Copy + Eq> {
    fn get_prim_value(&self) -> PrimValues;
}

pub trait NewPrimValues {
    fn new(z3_val: &Dynamic) -> Self;
}

/// Z3Solver 是一个封装了 Z3 的求解器的结构体
pub struct Z3Solver<'ctx, Identifier: VarIndex + Clone + Eq + Hash> {
    ctx: &'ctx Context,
    solver: z3::Solver<'ctx>,
    synth_fun: Option<z3::RecFuncDecl<'ctx>>,
    defined_funs: HashMap<Identifier, z3::RecFuncDecl<'ctx>>,
    declared_vars: HashMap<Identifier, z3::ast::Dynamic<'ctx>>,
}

impl<'ctx, Identifier: VarIndex + Clone + Eq + Hash + Debug> Z3Solver<'ctx, Identifier> {
    /// 创建一个新的 Z3Solver
    /// 里面已经包含了所有的约束, 但是约束里的 f 是未知的
    /// 你需要传入一个 'ctx 的 Z3 Context
    pub fn new<
        PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug,
        Types: GetZ3Type<'ctx> + Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    >(
        define_funs: &[DefineFun<Identifier, PrimValues, Types, FunctionVar, Context>],
        declare_vars: &[DeclareVar<Identifier, Types>],
        synth_fun: &SynthFun<Identifier, PrimValues, Types>,
        constraints: &[Constraint<Identifier, PrimValues>],
        ctx: &'ctx z3::Context,
    ) -> Self {

        let mut z3_solver: Z3Solver<'ctx, Identifier> = Z3Solver {
            ctx: ctx,
            solver: z3::Solver::new(ctx),
            synth_fun: None,
            defined_funs: HashMap::new(),
            declared_vars: HashMap::new(),
        };

        for defined_fun in define_funs {
            let decl = defined_fun.get_z3_decl(&ctx, &z3_solver);
            z3_solver.defined_funs.insert(defined_fun.var_index.clone(), decl);
        }

        // 我只需要先建立一个 Decl 就好了
        let synth_fun_decl = synth_fun.get_z3_decl(&ctx, &z3_solver);
        z3_solver.synth_fun = Some(synth_fun_decl);

        let mut declared_vars = HashMap::new();
        for declare_var in declare_vars {
            let z3_decl = declare_var.get_z3_var(&ctx, &z3_solver);
            declared_vars.insert(declare_var.get_id(), z3_decl);
        }

        let mut assert = z3::ast::Bool::from_bool(&ctx, true);
        for constraint in constraints {
            let z3_constraint = constraint.get_z3_assert(&ctx, &z3_solver);
            assert = z3::ast::Bool::and(&ctx, &[&z3_constraint, &assert]);
        }
        z3_solver.solver.assert(&assert.not());

        z3_solver
    }

    /// 传递进来一个已经填充好的 SynthFun，返回一个 SAT or CounterExample
    /// 应该传递进来的是一个 BasicFun
    pub fn get_counterexample<
        PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues,
        Types: GetZ3Type<'ctx> + Clone,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>,
    >(
        &mut self,
        synth_fun: &BasicFun<Identifier, PrimValues, Types, FunctionVar, Context>,
    ) -> Result<HashMap<Identifier, PrimValues>, String> {
        self.solver.push(); // 首先进入一个新的作用域
        let args = synth_fun.args.iter().map(|(id, ty)| {
            let z3_decl = get_z3_decl_with_type(self.ctx, id.clone(), ty.clone());
            z3_decl
        }).collect::<Vec<_>>();
        let args_ref = args.iter().map(|x| x as &dyn Ast).collect::<Vec<_>>();
        let args_array = args_ref.as_slice();
        let args_hashmap: HashMap<Identifier, &dyn Ast<'ctx>> = synth_fun
                .args
                .iter()
                .zip(args_ref.iter()) // Combine the self_args and args
                .map(|((id, _ty), arg)| (id.clone(), *arg)) // Create (Identifier, &dyn Ast<'ctx>)
                .collect();

        let synth_fun_expr = synth_fun.get_z3_expr(self.ctx, &args_hashmap, self);

        self.synth_fun.as_ref().unwrap().add_def(args_array, &synth_fun_expr);

        /* 
        let eq_constraint = self
            .synth_fun
            .unwrap()
            .apply(args_ref)
            ._eq(&synth_fun_expr.apply(args_ref));

        let quantifier = z3::ast::forall_const(&self.ctx, &args, &[], &eq_constraint);

        self.solver.assert(&quantifier);*/

        let res = self.solver.check();
        match res {
            z3::SatResult::Unsat => {
                self.solver.pop(1);
                return Err("Synth Function Passed All Constraints".to_string());
            }
            z3::SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut result = HashMap::new();
                for (id, _) in synth_fun.args {
                    let z3_var = self.declared_vars.get(id).unwrap();
                    let z3_value = model.eval(z3_var, true).unwrap();
                    let value = z3_value.get_prim_value();
                    result.insert(id.clone(), value);
                }
                self.solver.pop(1);
                return Ok(result);
            }
            _ => {
                self.solver.pop(1);
                return Err("Solver Unknown".to_string());
            }
        }
    }

    /// 得到一个函数的定义, 是一个引用
    pub fn get_func_decl(&self, id: &Identifier) -> &z3::RecFuncDecl<'ctx> {
        let func = self.defined_funs.get(id);
        match func {
            Some(f) => f,
            None => panic!("Function Not Found"),
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

impl<'ctx, PrimValues: GetZ3Value<'ctx> + Copy + Eq + Debug + NewPrimValues> GetPrimValue<'ctx, PrimValues>
    for z3::ast::Dynamic<'ctx>
{
    fn get_prim_value(&self) -> PrimValues {
        PrimValues::new(&self)
    }
}

pub fn get_z3_decl_with_type<'ctx, Identifier: VarIndex + Clone + Eq + Hash, Types: GetZ3Type<'ctx>>(
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


