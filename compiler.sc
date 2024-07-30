import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 



// typing
type Ty = String
type TyEnv = Map[String, Ty]

// initial typing environment
val initialEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
                                "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void")

val typeConversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")

// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String, ty: Ty = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KDouble(d: Double) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal, ty: Ty = "UNDEF") extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp

def typ_val(v: KVal, ts: TyEnv) : KVal = v match {
  case KVar(s, "UNDEF") => KVar(s, ts(s))
  case KNum(i) => KNum(i)
  case KDouble(d) => KDouble(d)
  case Kop(o, v1, v2, "UNDEF") => Kop(o, v1, v2, typ_val2(Kop(o, v1, v2, "UNDEF"), ts))
  case _ => v
}

def typ_val2(v: KVal, ts: TyEnv) : Ty = v match {
  case KNum(i) => "Int"
  case KDouble(d) => "Double"
  case KVar(s, "UNDEF") => ts(s)
  case KVar(s, ty) => ty 
  case Kop(o, v1, v2, "UNDEF") => typ_val2(v1, ts)
  case Kop(o, v1, v2, ty) => ty  
  case KCall(o, vrs) => ts(o)
}

// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => k(KVar(s)) 
  case Num(i) => k(KNum(i))
  case ChConst(c) => k(KNum(c))
  case FNum(i) => k(KDouble(i))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
}   

//initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)


// prelude
val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_int = private constant [3 x i8] c"%d\00"
@.str_c = private constant [3 x i8] c"%c\00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_int, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @print_char(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_c, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x)
  ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILT-IN FUNCTIONS (prelude)
"""

// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

extension (sc: StringContext) {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop (op: String) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
}

// compile K values
def compile_val(v: KVal, env: TyEnv, x: String) : String = typ_val(v, env) match {
  case KNum(i) => s"$i"
  case KDouble(d) => s"$d"
  case KVar(s, ty) if s.charAt(0).isUpper => s"load ${typeConversion(ty)}, ${typeConversion(ty)}* @$s"
  case KVar(s, ty) => s"%$s"
  case Kop(op, x1, x2, ty) => {
    val globalVarString = compile_global_var(x1, env)
    val globalVarString2 = compile_global_var(x2, env)
    if ((globalVarString != "") & (globalVarString2 != "") ) {
      val compiledString = globalVarString ++ globalVarString2
      val y = globalVarString.substring(0, globalVarString.indexOf('=')).trim()
      val z = globalVarString2.substring(0, globalVarString2.indexOf('=')).trim()
      if (ty == "Int") compiledString ++ i"%$x = ${compile_op(op)} $y, $z"
      else compiledString ++ i"%$x = ${compile_dop(op)} $y, $z"
    } 
    else if ((globalVarString == "") & (globalVarString2 != "") ) {
      val compiledString = globalVarString2
      val z = globalVarString2.substring(0, globalVarString2.indexOf('=')).trim()
      if (ty == "Int") compiledString ++ i"%$x = ${compile_op(op)} ${compile_val(x1, env, x)}, $z"
      else compiledString ++ i"%$x = ${compile_dop(op)} ${compile_val(x1, env, x)}, $z"
    }
    else if ((globalVarString != "") & (globalVarString2 == "") ) {
      val compiledString = globalVarString
      val y = globalVarString.substring(0, globalVarString.indexOf('=')).trim()
      if (ty == "Int") compiledString ++ i"%$x = ${compile_op(op)} $y, ${compile_val(x2, env, x)}"
      else compiledString ++ i"%$x = ${compile_dop(op)} $y, ${compile_val(x2, env, x)}"
    }
    else {
      if (ty == "Int") s"${compile_op(op)} ${compile_val(x1, env, x)}, ${compile_val(x2, env, x)}"
      else s"${compile_dop(op)} ${compile_val(x1, env, x)}, ${compile_val(x2, env, x)}"
    }
  }
  case KCall(x1, args) => {
    val globalVars = args.map(x => compile_global_var(x, env).trim())
    val filteredGlobalVars = globalVars.filter(x => x != "")
    if (!filteredGlobalVars.isEmpty) {
      val updatedArgs = ((args.zip(globalVars)).map{
        case (kval, "") => kval   
        case (KVar(s, ty), compiledS) => KVar(compiledS.substring(compiledS.indexOf('%') + 1, compiledS.indexOf('=')).trim(), env(s))
      })
      val compiledString = filteredGlobalVars.mkString(s"", "\n   ", "\n   ")
      val arguments = for arg <- updatedArgs yield typeConversion(typ_val2(arg, env)) ++ " " ++ compile_val(arg, env, x)
      compiledString ++ s"call ${typeConversion(env(x1))} @$x1 (${arguments.mkString(", ")})"
    }
    else {
      val arguments = for arg <- args yield typeConversion(typ_val2(arg, env)) ++ " " ++ compile_val(arg, env, x)
      s"call ${typeConversion(env(x1))} @$x1 (${arguments.mkString(", ")})"
    }
  }
}

def compile_global_var(v: KVal, env: TyEnv) : String = typ_val(v, env) match {
  case KVar(s, ty) if s.charAt(0).isUpper => {
    val x = Fresh("tmp")
    i"%$x = load ${typeConversion(ty)}, ${typeConversion(ty)}* @$s"
  }
  case _ => ""
}

// compile K expressions
def compile_exp(a: KExp, env: TyEnv) : String = a match {
  case KReturn(v) => {
    if (typ_val2(v, env) == "Void") i"ret void"
    else i"ret ${typeConversion(typ_val2(v, env))} ${compile_val(v, env, "")}"
  }
  case KLet(x: String, v: KVal, e: KExp) => {
    val updated_env = env + (x -> typ_val2(v, env))
    if (typ_val2(v, env) == "Void") {
      i"${compile_val(v, env, x)}" ++ compile_exp(e, updated_env)
    }
    else {
      val compiledString = compile_val(v, env, x)
      if (compiledString.contains("load")) compiledString ++ compile_exp(e, updated_env)
      else i"%$x = ${compile_val(v, env, x)}" ++ compile_exp(e, updated_env)

    }
  }
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1, env) ++
    l"\n$else_br" ++ 
    compile_exp(e2, env)
  }
}

// compile function for declarations and main
def compile_decl(d: Decl, env: TyEnv): (String, TyEnv) = d match {
  case Const(name, v) => {
    val updatedEnv = env + (name -> "Int")
    val compiledString = m"@$name = global i32 $v" ++ "\n"
    (compiledString, updatedEnv)
  }
  case FConst(name, x) => {
    val updatedEnv = env + (name -> "Double")
    val compiledString = m"@$name = global double $x" ++ "\n"
    (compiledString, updatedEnv)
  }
  case Def(name, args, ty, body) => {
    val updatedEnv = env + (name -> ty)
    val updatedEnv2 = update_env(updatedEnv, args)
    val arguments = for arg <- args yield typeConversion(arg._2) ++ " %" ++ arg._1
    val compiledString = m"define ${typeConversion(ty)} @$name (${arguments.mkString(", ")}) {" ++
      compile_exp(CPSi(body), updatedEnv2) ++
    m"}\n"
    (compiledString, updatedEnv2)
  }
  case Main(body) => {
    val compiledString = m"define i32 @main() {" ++
      compile_exp(CPS(body)(_ => KReturn(KNum(0))), env) ++
    m"}\n"
    (compiledString, env)
  }
}

def update_env(env: TyEnv, args: List[(String, String)]) : TyEnv = args match {
  case Nil => env
  case arg::rest => update_env(env + (arg._1 -> (arg._2:Ty)), rest)
}

// main compilation function
def fun_compile(prog: List[Decl]): String = {
  val (_, result) = prog.foldLeft((initialEnv, prelude)) {
    case ((env, acc), decl) =>
      val (compiledString, updatedEnv) = compile_decl(decl, env)
      (updatedEnv, acc + compiledString)
  }
  result
}

// @main
// def test() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/test.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   println(tks)
//   val ast = parse_tks(tks)
//   println(ast)
//   println("\n")
//   val e10 = List(Def("fact",List(("n","Int"), ("b", "Double")),"Int",If(Bop("==",Var("n"),Num(0)),Num(1),Aop("*",Var("n"),Call("fact",List(Aop("-",Var("n"),Num(1))))))))
//   val e1 = List(FConst("Ymin",-1.3), FConst("Ymax",1.3), FConst("Ystep",0.05), FConst("Xmin",-2.1), FConst("Xmax",1.1), FConst("Xstep",0.02), Const("Maxiters",1000), Def("m_iter",List(("m","Int"), ("x","Double"), ("y","Double"), ("zr","Double"), ("zi","Double")),"Void",If(Bop("<=",Var("Maxiters"),Var("m")),Call("print_star",List()),If(Bop("<=",FNum(4.0),Aop("+",Aop("*",Var("zi"),Var("zi")),Aop("*",Var("zr"),Var("zr")))),Call("print_space",List()),Call("m_iter",List(Aop("+",Var("m"),Num(1)), Var("x"), Var("y"), Aop("+",Var("x"),Aop("-",Aop("*",Var("zr"),Var("zr")),Aop("*",Var("zi"),Var("zi")))), Aop("+",Aop("*",FNum(2.0),Aop("*",Var("zr"),Var("zi"))),Var("y"))))))))
//   println(fun_compile(e1))
// }

// @main
// def fact() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/fact.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   val ast = parse_tks(tks)
//   println(ast)
//   println(fun_compile(ast))
// }

// @main
// def hanoi() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/hanoi.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   val ast = parse_tks(tks)
//   println(ast)
//   println(fun_compile(ast))
// }

// @main
// def mand() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/mand.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   val ast = parse_tks(tks)
//   println(ast)
//   println(fun_compile(ast))
// }

// @main
// def mand2() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/mand2.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   val ast = parse_tks(tks)
//   println(ast)
//   println(fun_compile(ast))
// }

// @main
// def sqr() = {
//   val source = scala.io.Source.fromFile("C:/Users/brjal/Documents/King's College London Year 3 Courseworks/Compilers and Formal Languages - CFL/assignment2023cfl5-BrianJalleh/cw5/sqr.fun")
//   val lines = try source.mkString finally source.close()
//   val tks = tokenise(lines)
//   val ast = parse_tks(tks)
//   println(ast)
//   println(fun_compile(ast))
// }