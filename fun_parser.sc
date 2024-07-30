// A parser for the Fun language
//================================
//
// call with 
//
//     amm fun_parser.sc fact.fun

//     amm fun_parser.sc defs.fun
//
// this will generate a parse-tree from a list
// of tokens

import scala.language.implicitConversions    
import scala.language.reflectiveCalls

import $file.fun_tokens, fun_tokens._ 


// Parser combinators
//    type parameter I needs to be of Seq-type
//
type IsSeq[I] = I => Seq[_]

/*
abstract class Parser[I, T](using is: I => Seq[_])  {
  def parse(in: I): Set[(T, I)]  

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if is(tl).isEmpty) yield hd
}
*/


abstract class Parser[I, T](using is: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(p => is(p._2).isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { println (s"Parse Error\n${err.minBy(p => is(p._2).length)}") ; sys.exit(-1) }
    }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

// parser combinators

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}



// more convenient syntax for parser combinators
extension [I : IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

// Parser for parameters and their types when functions are defined
def ParamParser[I, T, Q, R, S](p: => Parser[I, T], s: => Parser[I, Q], r: => Parser[I, R], q: => Parser[I, S])(using is: I => Seq[_]): Parser[I, List[(T, R)]] = {
  (p ~ s ~ r ~ q ~ ParamParser(p, s, r, q)).map{ case (w:T) ~ (v:Q) ~ (x:R) ~ (y:S) ~ (z:List[(T,R)]) => (w, x) :: z } ||
  (p ~ s ~ r).map{case (x:T) ~ _ ~ (y:R) => List((x, y))}
}

// Parser for arguments when functions are called
def ArgsParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(using is: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ArgsParser(p, q)).map{ case (x:T) ~ (y:S) ~ (z:List[T]) => x :: z } ||
  (p.map[List[T]]{s => List(s)})
}

case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) : Parser[List[Token], Token] = TokParser(t)


extension (t: Token) {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def map[S] (f: => Token => S) = new MapParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

// atomic parser for integers
case object IntegerParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_INTEGER(n)::ts => Set((n, ts)) 
    case _ => Set()
  }
}

// atomic parser for doubles
case object DoubleParser extends Parser[List[Token], Double] {
  def parse(ts: List[Token]) = ts match {
    case T_DOUBLE(n)::ts => Set((n, ts)) 
    case _ => Set()
  }
}

// atomic parser for identifiers
case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set()
  }
}

// atomic parser for global identifiers
case object GlobalIdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_GLOBALID(s)::ts => Set((s, ts)) 
    case _ => Set()
  }
}

// atomic parser for strings
case object StrParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_STRING(str)::ts => Set((str, ts))
    case _ => Set()
  }
}

// atomic parser for types
case object TypeParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_TYPE(str)::ts => Set((str, ts))
    case _ => Set()
  }
}

// atomic parser for character constants
case object CharacterParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_CHARACTER("'\\n'")::ts => Set((10, ts))
    case T_CHARACTER("'\\t'")::ts => Set((9, ts))
    case T_CHARACTER("'\\r'")::ts => Set((13, ts))
    case T_CHARACTER(str)::ts => Set((str.charAt(1).toInt, ts))
    case _ => Set()
  }
}



// Abstract Syntax Trees for the typed Fun-language
// (this can be part of the parser file, if more convenient)

abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String, String)], ty: String, body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String, v: Int) extends Decl
case class FConst(name: String, x: Double) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp  // integer numbers
case class FNum(i: Double) extends Exp  // float numbers
case class ChConst(c: Int) extends Exp  // character constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp  // expressions separated by semicolons
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp



// Grammar Rules for the Fun language

// arithmetic expressions
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ (Exp || Block) ~ T_KWD("else") ~ (Exp || Block)).map{ case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (L ~ T_SEMI ~ Exp).map{ case x ~ _ ~ y => Sequence(x, y): Exp } || L
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp).map{ case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp).map{ case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T).map{ case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T).map{ case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T).map{ case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_PAREN("(") ~ ArgsParser(Exp, T_COMMA) ~ T_PAREN(")")).map
    { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (IdParser ~ T_PAREN("(") ~ T_PAREN(")")).map
    { case x ~ _ ~ _ => Call(x, List()): Exp } ||
  (T_PAREN("(") ~ Exp ~ T_PAREN(")")).map{ case _ ~ y ~ _ => y: Exp } || 
  (IdParser || GlobalIdParser).map{ case x => Var(x): Exp } || 
  IntegerParser.map{ case x => Num(x): Exp } ||
  DoubleParser.map{ case x => FNum(x): Exp } ||
  CharacterParser.map{ case x => ChConst(x): Exp } ||
  (T_KWD("print_string") ~ T_PAREN("(") ~ StrParser ~ T_PAREN(")")).map
    { case x ~ _ ~ z ~ _ => print_string(z.substring(1, z.length - 1)): Exp } ||
  (T_KWD("skip") ~ T_PAREN("(") ~ T_PAREN(")")).map{ case _ ~ _ ~ _ => Call("skip", List()): Exp } ||
  T_KWD("skip").map{ case _ => Call("skip", List()): Exp }

def print_string(s: String) : Exp = {
  if (s.length == 1) Call("print_char", List(ChConst(s.charAt(0).toInt)))
  else Sequence(Call("print_char", List(ChConst(s.charAt(0).toInt))), print_string(s.tail))
}

// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp).map{ case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp).map{ case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP(">=") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", z, x): BExp }  

// blocks (expression enclosed in curly braces)
lazy val Block: Parser[List[Token], Exp] =
  (T_PAREN("{") ~ Exp ~ T_PAREN("}")).map{ case _ ~ y ~ _ => y: Exp }

lazy val Vals: Parser[List[Token], Decl] =
  (T_KWD("val") ~ GlobalIdParser ~ T_COLON ~ TypeParser ~ T_OP("=") ~ DoubleParser).map{ case _ ~ x ~ _ ~ _ ~ _ ~ z => FConst(x, z): Decl } ||
  (T_KWD("val") ~ GlobalIdParser ~ T_COLON ~ TypeParser ~ T_OP("=") ~ IntegerParser).map{ case _ ~ x ~ _ ~ _ ~ _ ~ z => Const(x, z): Decl }

lazy val Defn: Parser[List[Token], Decl] =
   (T_KWD("def") ~ IdParser ~ T_PAREN("(") ~ ParamParser(IdParser, T_COLON, TypeParser, T_COMMA) ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ (Exp || Block)).map{ case _ ~ w ~ _ ~ x ~ _ ~ _ ~ y ~ _ ~ z => Def(w, x, y, z): Decl } ||
   (T_KWD("def") ~ IdParser ~ T_PAREN("(") ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ (Exp || Block)).map{ case _ ~ w ~ _ ~ _ ~ _ ~ y ~ _ ~ z => Def(w, List(), y, z): Decl }

lazy val Prog: Parser[List[Token], List[Decl]] =
  (Vals ~ T_SEMI ~ Prog).map{ case x ~ _ ~ z => x :: z : List[Decl] } ||
  (Defn ~ T_SEMI ~ Prog).map{ case x ~ _ ~ z => x :: z : List[Decl] } ||
  ((Exp || Block).map((s) => List(Main(s)) : List[Decl]))



// Reading tokens and Writing parse trees

// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._

def parse_tks(tks: List[Token]) : List[Decl] = 
  Prog.parse_single(tks)

//@doc("Parses a file.")
@main
def main(fname: String) : Unit = {
  val tks = tokenise(os.read(os.pwd / fname))
  println(parse_tks(tks))
}


