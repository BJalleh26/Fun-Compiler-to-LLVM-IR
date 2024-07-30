// A tokeniser for the Fun language
//==================================
//
// call with 
//
//     amm fun_tokens.sc fact.fun
//
//     amm fun_tokens.sc defs.fun
//

 

import scala.language.implicitConversions    
import scala.language.reflectiveCalls 

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 
  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

extension (s: String) {
  def $ (r: Rexp) = RECD(s, r)
}

extension (r: Rexp) {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}


def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(_) => true
  case NTIMES(r1, n) => if (n == 0) true else nullable(r1)
  case RECD(_, r1) => nullable(r1)
}

def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RANGE(cs) =>
    if (cs.contains(c)) ONE
    else ZERO
  case PLUS(r1) => SEQ(der(c,r1), STAR(r1))
  case OPTIONAL(r1) => ALT(der(c, r1), ZERO)
  case NTIMES(r1, n) => 
    if (n == 0) ZERO else SEQ(der(c, r1), NTIMES(r1, n-1))
  case RECD(_, r1) => der(c, r1)
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString  
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => if (nullable(r)) Left(mkeps(r)) else Right(Empty)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), Left(v)) => Left(inj(r, c, v))
  case (OPTIONAL(r), Right(v)) => Right(inj(r, c, v))
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case _ => { println ("Injection error") ; sys.exit(-1) } 
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else { println ("Lexing Error") ; sys.exit(-1) } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))


// The Lexing Rules for the Fun Language
val SYMBOLS: Rexp = RANGE(('a' to 'z').toSet | ('A' to 'Z').toSet) | RANGE(Set('.', '_', '>', '<', '=', ';', ',', '\\', ':'))
val SYM : Rexp = RANGE(('a' to 'z').toSet) | "T" | "_"
val PARENS : Rexp = RANGE(Set('(', ')', '{', '}'))
val DIGIT : Rexp = RANGE(('0' to '9').toSet)
val ID : Rexp = SYM ~ (SYM | DIGIT).% 
val GLOBALID : Rexp = (RANGE(('A' to 'Z').toSet)) ~ (SYM | DIGIT).%
val INTEGER = OPTIONAL("-") ~ ((RANGE(('1' to '9').toSet) ~ STAR(DIGIT)) | CHAR('0'))
val DOUBLE = OPTIONAL("-") ~ ((RANGE(('1' to '9').toSet) ~ STAR(DIGIT)) | CHAR('0')) ~ "." ~ PLUS(DIGIT)
val KEYWORD : Rexp = "if" | "then" | "else" | "def" | "val" | "print_string" | "skip"
val TYPE : Rexp = "Int" | "Void" | "Double"
val SEMI: Rexp = ";"
val COLON: Rexp = ":"
val OP: Rexp = "=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" ") | "\n" | "\t" | "\r"
val STRING : Rexp = CHAR('"') ~ STAR(SYMBOLS | DIGIT | WHITESPACE | "\n" | PARENS | OP) ~ CHAR('"')
val CHARACTER : Rexp = "'" ~ (SYMBOLS | DIGIT | PARENS | "\\n" | "\\t" | "\\r" | "-" | "+" | "*" | "/" | "%" | " " | "'" | "\"") ~ "'"
val COMMA : Rexp = ","
val EOL : Rexp = "\n" | "\r\n"
val ALL : Rexp = SYMBOLS | DIGIT | OP | PARENS | " " | "\"" | "'"
val ALL2 : Rexp = ALL | EOL
val COMMENT : Rexp = ("/*" ~ ALL2.% ~ "*/") | ("//" ~ ALL.% ~ (EOL | "" | PLUS(" ")))


val FUN_REGS = (("k" $ KEYWORD) | 
                  ("t" $ TYPE) |
                  ("g" $ GLOBALID) |
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("str" $ STRING) |
                  ("chr" $ CHARACTER) |
                  ("n" $ INTEGER) |
                  ("d" $ DOUBLE) | 
                  ("s" $ SEMI) | 
                  ("c" $ COMMA) |
                  ("cl" $ COLON) |
                  ("p" $ PARENS) |
                  ("w" $ (WHITESPACE | COMMENT))).%



// The tokens for the Fun language

abstract class Token extends Serializable 
case object T_SEMI extends Token
case object T_COMMA extends Token
case object T_COLON extends Token
case class T_PAREN(s: String) extends Token
case class T_STRING(s: String) extends Token
case class T_CHARACTER(s: String) extends Token
case class T_ID(s: String) extends Token
case class T_GLOBALID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_INTEGER(n: Int) extends Token
case class T_DOUBLE(n: Double) extends Token
case class T_KWD(s: String) extends Token
case class T_TYPE(s: String) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KWD(s)
  case ("t", s) => T_TYPE(s)
  case ("g", s) => T_GLOBALID(s)
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_INTEGER(s.toInt)
  case ("d", s) => T_DOUBLE(s.toDouble)
  case ("s", _) => T_SEMI
  case ("c", _) => T_COMMA
  case ("cl", _) => T_COLON
  case ("p", s) => T_PAREN(s)
  case ("str", s) => T_STRING(s)
  case ("chr", s) => T_CHARACTER(s)
}


def tokenise(s: String) : List[Token] = {
  val tks = lexing_simp(FUN_REGS, s).collect(token)
  if (tks.length != 0) tks
  else { println (s"Tokenise Error") ; sys.exit(-1) }     
}