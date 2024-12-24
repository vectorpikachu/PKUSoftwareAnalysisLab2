use z3::{ast::{Ast, Bool, Dynamic}, SortKind};


/// 检查当前是否是一个 Z3 的内建函数
pub fn check_z3_builtin<'ctx>(
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
        "/" => {
            arg_num_check(args, 2, "/");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => {
                    if args[1].as_int().unwrap().as_i64().unwrap() == 0 {
                        return Err("Division by zero".to_string());
                    }
                    Ok((args[0].as_int().unwrap() / args[1].as_int().unwrap()).into())
                }
                _ => Err(format!("Unsupported type in /: {:?}", kind)),
            }
        }
        "mod" => {
            arg_num_check(args, 2, "mod");
            let kind = args[0].get_sort().kind();
            match kind {
                SortKind::Int => Ok((args[0].as_int().unwrap() % args[1].as_int().unwrap()).into()),
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
        "=>" => {
            arg_num_check(args, 2, "=>");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::Bool {
                return Err(format!("Expected Bool in =>, got {:?}", kind));
            }
            Ok(args[0].as_bool().unwrap().implies(&args[1].as_bool().unwrap()).into())
        }
        "bvnot" => {
            // bitwise negation
            arg_num_check(args, 1, "bvnot");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvnot, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvnot().into())
        }
        "bvneg" => {
            arg_num_check(args, 1, "bvneg");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvneg, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvneg().into())
        }
        "bvand" => {
            arg_num_check(args, 2, "bvand");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvand, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvand(&args[1].as_bv().unwrap()).into())
        }
        "bvor" => {
            arg_num_check(args, 2, "bvor");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvor, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvor(&args[1].as_bv().unwrap()).into())
        }
        "bvxor" => {
            arg_num_check(args, 2, "bvxor");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvxor, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvxor(&args[1].as_bv().unwrap()).into())
        }
        "bvadd" => {
            arg_num_check(args, 2, "bvadd");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvadd, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvadd(&args[1].as_bv().unwrap()).into())
        }
        "bvsub" => {
            arg_num_check(args, 2, "bvsub");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsub, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsub(&args[1].as_bv().unwrap()).into())
        }
        "bvmul" => {
            arg_num_check(args, 2, "bvmul");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvmul, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvmul(&args[1].as_bv().unwrap()).into())
        }
        "bvudiv" => {
            arg_num_check(args, 2, "bvudiv");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvudiv, got {:?}", kind));
            }
            if args[1].as_bv().unwrap().as_i64().unwrap() == 0 {
                return Err("Division by zero".to_string());
            }
            Ok(args[0].as_bv().unwrap().bvudiv(&args[1].as_bv().unwrap()).into())
        }
        "bvsdiv" => {
            arg_num_check(args, 2, "bvsdiv");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsdiv, got {:?}", kind));
            }
            if args[1].as_bv().unwrap().as_i64().unwrap() == 0 {
                return Err("Division by zero".to_string());
            }
            Ok(args[0].as_bv().unwrap().bvsdiv(&args[1].as_bv().unwrap()).into())
        }
        "bvurem" => {
            arg_num_check(args, 2, "bvurem");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvurem, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvurem(&args[1].as_bv().unwrap()).into())
        }
        "bvsrem" => {
            arg_num_check(args, 2, "bvsrem");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsrem, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsrem(&args[1].as_bv().unwrap()).into())
        }
        "bvshl" => {
            arg_num_check(args, 2, "bvshl");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvshl, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvshl(&args[1].as_bv().unwrap()).into())
        }
        "bvsmod" => {
            arg_num_check(args, 2, "bvsmod");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsmod, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsmod(&args[1].as_bv().unwrap()).into())
        }
        "bvult" => {
            arg_num_check(args, 2, "bvult");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvult, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvult(&args[1].as_bv().unwrap()).into())
        }
        "bvslt" => {
            arg_num_check(args, 2, "bvslt");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvslt, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvslt(&args[1].as_bv().unwrap()).into())
        }
        "bvule" => {
            arg_num_check(args, 2, "bvule");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvule, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvule(&args[1].as_bv().unwrap()).into())
        }
        "bvsle" => {
            arg_num_check(args, 2, "bvsle");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsle, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsle(&args[1].as_bv().unwrap()).into())
        }
        "bvuge" => {
            arg_num_check(args, 2, "bvuge");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvuge, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvuge(&args[1].as_bv().unwrap()).into())
        }
        "bvsge" => {
            arg_num_check(args, 2, "bvsge");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsge, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsge(&args[1].as_bv().unwrap()).into())
        }
        "bvugt" => {
            arg_num_check(args, 2, "bvugt");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvugt, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvugt(&args[1].as_bv().unwrap()).into())
        }
        "bvsgt" => {
            arg_num_check(args, 2, "bvsgt");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvsgt, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvsgt(&args[1].as_bv().unwrap()).into())
        }
        "bvlshr" => {
            arg_num_check(args, 2, "bvlshr");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvlshr, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvlshr(&args[1].as_bv().unwrap()).into())
        }
        "bvashr" => {
            arg_num_check(args, 2, "bvashr");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in bvashr, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().bvashr(&args[1].as_bv().unwrap()).into())
        }
        "concat" => {
            arg_num_check(args, 2, "concat");
            let kind = args[0].get_sort().kind();
            if kind != SortKind::BV {
                return Err(format!("Expected BV in concat, got {:?}", kind));
            }
            Ok(args[0].as_bv().unwrap().concat(&args[1].as_bv().unwrap()).into())
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
        "+" | "-" | "*" | "mod" | "/" => {
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
        "bvnot" | "bvneg" => {
            let arg_kind = args[0].get_sort().kind();
            if arg_kind != SortKind::BV {
                panic!("Expected BV in {}, got {:?}", func_name, arg_kind);
            }
        }
        "bvand" | "bvor" | "bvadd" | "bvmul" | "bvudiv" | "bvsdiv" | "bvurem" | "bvsrem" | "bvshl" | "bvlshr" | "bvashr" | "concat" 
            | "bvult" | "bvslt" | "bvule" | "bvsle" | "bvuge" | "bvsge" | "bvugt" | "bvsgt" => {
            let arg1_kind = args[0].get_sort().kind();
            let arg2_kind = args[1].get_sort().kind();
            if arg1_kind != arg2_kind {
                panic!("Expected same type in {}, got {:?} and {:?}", func_name, arg1_kind, arg2_kind);
            }
        }
        _ => {}
    }
}