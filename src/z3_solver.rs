use std::{collections::HashMap, fmt::Debug, hash::Hash, result::Result};

use z3::{Sort, SortKind};
use z3::{self, ast::Ast};

use z3::ast::Dynamic;

use crate::base::{function::{PositionedExecutable, VarIndex}, language::{Constraint, DeclareVar, DefineFun, SynthFun}, scope::Scope};

pub trait GetZ3Type {
    fn get_z3_type(&self) -> z3::Sort;
}

pub trait GetZ3Value {
    fn get_z3_value(&self) -> Dynamic;
}

pub trait GetZ3Decl {
    /// 对于 DefineFun 来说，返回的是一个 RecFuncDecl + 它的定义
    fn get_z3_decl(&self, ctx: &z3::Context) -> z3::RecFuncDecl;
}

pub trait GetZ3Ast {
    fn get_z3_ast(&self, ctx: &z3::Context) -> Dynamic;
}

pub trait GetZ3Expr<
    Identifier: VarIndex + Clone + Eq,
> {
    fn get_z3_expr(&self, ctx: &z3::Context, args: &HashMap<Identifier, &dyn Ast>) -> Dynamic;
}

pub trait GetPrimValue<
    PrimValues: GetZ3Value + Copy + Eq,
> {
    fn get_prim_value(&self) -> PrimValues;
}

pub trait NewPrimValues {
    fn new(sort_kind: z3::SortKind) -> Self;
}

/// Z3Solver 是一个封装了 Z3 的求解器的结构体
pub struct Z3Solver<'ctx,
    Identifier: VarIndex + Clone + Eq + Hash,
> {
    ctx: z3::Context,
    solver: z3::Solver<'ctx>,
    synth_fun: z3::RecFuncDecl<'ctx>,
    defined_funs: HashMap<Identifier, z3::RecFuncDecl<'ctx>>,
    declared_vars: HashMap<Identifier, z3::ast::Dynamic<'ctx>>,
}

impl<'ctx, Identifier: VarIndex + Clone + Eq + Hash + Debug> Z3Solver<'ctx, Identifier> {

    /// 创建一个新的 Z3Solver
    /// 里面已经包含了所有的约束, 但是约束里的 f 是未知的
    pub fn new<
        PrimValues: GetZ3Value + Copy + Eq + Debug,
        Types: GetZ3Type,
        FunctionVar: PositionedExecutable<Identifier, PrimValues, PrimValues> + Clone,
        Context: Scope<Identifier, Types, PrimValues, FunctionVar>
    >(
        define_funs: &[DefineFun<Identifier, PrimValues, Types, FunctionVar, Context>],
        declare_vars: &[DeclareVar<Identifier, PrimValues>],
        synth_fun: &SynthFun<Identifier, PrimValues, Types>,
        constraints: &[Constraint<Identifier, PrimValues>],
    ) -> Self {
        let ctx = z3::Context::new(&Default::default());
        let solver = z3::Solver::new(&ctx);

        let mut defined_funs = HashMap::new();
        for defined_fun in define_funs {
            let z3_decl = defined_fun.get_z3_decl(&ctx);
            defined_funs.insert(defined_fun.var_index, z3_decl);
        }

        // 我只需要先建立一个 Decl 就好了
        let synth_fun_decl = synth_fun.get_z3_decl(&ctx);

        let mut declared_vars = HashMap::new();
        for declare_var in declare_vars {
            let z3_decl = declare_var.get_z3_decl(&ctx);
            declared_vars.insert(declare_var.get_id(), z3_decl);
        }
        
        let assert = z3::ast::Bool::from_bool(&ctx, true);
        for constraint in constraints {
            let z3_constraint = constraint.get_z3_ast(&ctx);
            assert = z3::ast::Bool::and(&ctx, 
                &[&z3_constraint, &assert]
            );
        }
        solver.assert(&assert.not());
        Z3Solver {
            ctx,
            solver,
            synth_fun:synth_fun_decl,
            defined_funs,
            declared_vars,
        }
    }

    /// 传递进来一个已经填充好的 SynthFun，返回一个 SAT or CounterExample
    pub fn get_counterexample<
        PrimValues: GetZ3Value + Copy + Eq + Debug + NewPrimValues,
        Types: GetZ3Type,
    >(
        &self,
        synth_fun: &SynthFun<Identifier, PrimValues, Types>
    ) -> Result<HashMap<Identifier, PrimValues>, String> {
        self.solver.push(); // 首先进入一个新的作用域
        let mut args = Vec::new();
        for arg in synth_fun.get_args() {
            let z3_arg = get_z3_decl_with_type(&self.ctx, arg.0, arg.1);
            args.push(z3_arg);
        }

        
        let synth_fun_expr = synth_fun.get_z3_expr(&self.ctx, &args);

        let eq_constraint = self.synth_fun.apply(&args.iter().collect::<Vec<_>>())._eq(&synth_fun_expr.apply(&args.iter().collect::<Vec<_>>()));
        
        let quantifier = z3::ast::forall_const(&self.ctx, &args, 
            &[],&eq_constraint);
        
        self.solver.assert(&quantifier);

        let res = self.solver.check();
        match res {
            z3::SatResult::Unsat => {
                self.solver.pop(1);
                return Err("Synth Function Passed All Constraints".to_string());
            },
            z3::SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut result = HashMap::new();
                for (id, _) in synth_fun.get_args() {
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
}

impl<'ctx,
    PrimValues: GetZ3Value + Copy + Eq + Debug + NewPrimValues,
> GetPrimValue<PrimValues> for z3::ast::Dynamic<'ctx> {
    fn get_prim_value(&self) -> PrimValues {
        PrimValues::new(self.sort_kind())
    }
}

pub fn get_z3_decl_with_type<'ctx,
    Identifier: VarIndex + Clone + Eq + Hash,
    Types: GetZ3Type,
>(ctx: &'ctx z3::Context, id: Identifier, ty: Types) -> z3::ast::Dynamic<'ctx> {
    let z3_ty = ty.get_z3_type();
    let z3_decl: Dynamic<'ctx> = match z3_ty.kind() {
        SortKind::Int => z3::ast::Int::new_const(ctx, id.to_name()).into(),
        SortKind::Bool => z3::ast::Bool::new_const(ctx, id.to_name()).into(),
        _ => panic!("Unsupported Type")
    };
    z3_decl
}
