/*
 * Copyright © 2019 University of Texas at Arlington
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package edu.uta.array

import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.token.StdTokens
import scala.util.matching.Regex


trait MyTokens extends StdTokens {
  case class LongLit ( chars: String ) extends Token
  case class DoubleLit ( chars: String ) extends Token
  case class CharLit ( chars: String ) extends Token
  case class InfixOpr ( chars: String ) extends Token
}

class MyLexical extends StdLexical with MyTokens {
  /* a parser for regular expressions */
  def regex ( r: Regex ): Parser[String]
      = new Parser[String] {
            def apply ( in: Input )
                = r.findPrefixMatchOf(in.source.subSequence(in.offset,in.source.length)) match {
                        case Some(matched)
                          => Success(in.source.subSequence(in.offset,in.offset+matched.end).toString,
                                     in.drop(matched.end))
                        case None => Failure("string matching regex `"+r+"' expected but "+in.first+" found",in)
                  }
      }

  override def token: Parser[Token] = infixOpr | longLit | doubleLit | charLit | super.token

  /* long integers */
  def longLit: Parser[Token]
      = regex("""[0-9]+[Ll]""".r) ^^ LongLit

  /* floating point numbers */
  def doubleLit: Parser[Token]
      = regex("""[0-9]*[\.][0-9]+([eE][+-]?[0-9]+)?[FfDd]?""".r) ^^ DoubleLit

  /* character literal */
  def charLit: Parser[Token]
      = regex("""'[^']'""".r) ^^ CharLit

  /* an infix operator can be any sequence of special chars, except delimiters, etc */ 
  def infixOpr: Parser[Token]
      = regex("""[^\s\w\$\(\)\[\]\{\}\'\"\`\.\;\,\\/]+""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else InfixOpr(s) }
}

object Parser extends StandardTokenParsers {
  var queryText: String = ""

  override val lexical = new MyLexical

  lexical.delimiters += ( "(" , ")" , "[", "]", "{", "}", "," , ":", ";", ".", "<-", "=>", "@", "::",
                          "||", "&&", "!", "=", "==", "<=", ">=", "<", ">", "!=", "+", "-", "*", "/", "%",
                          "^", "|", "&" )

  lexical.reserved += ("group", "by", "abstract", "do", "finally", "import", "until",
                       "object", "return", "trait", "var", "case", "else", "for", "lazy", "override",
                       "sealed", "try", "while", "catch", "extends", "forSome", "match", "package",
                       "super", "true", "with", "class", "false", "if", "new", "private", "this",
                       "type", "yield", "def", "final", "implicit", "null", "protected", "throw", "val")

  /* groups of infix operator precedence, from low to high */
  val operator_precedence: List[Parser[String]]
      = List( "||", "^", "&&"|"&", "<="|">="|"<"|">", "="|"=="|"!=", "+"|"-", "*"|"/"|"%" )

  /* all infix operators not listed in operator_precedence have the same highest precedence */  
  val infixOpr: Parser[String]
      = accept("infix operator",{ case t: lexical.InfixOpr => t.chars })
  val precedence: List[Parser[String]]
      = operator_precedence :+ infixOpr
  val allInfixOpr: Parser[String]
      = operator_precedence.fold(infixOpr)(_|_)

  /* group infix operations into terms based on the operator precedence, from low to high */
  def terms ( level: Int ): Parser[(Expr,Expr)=>Expr]
      = precedence(level) ^^
        { op => (x:Expr,y:Expr) => MethodCall(x,op,List(y)) }
  def infix ( level: Int ): Parser[Expr]
      = if (level >= precedence.length) conses
        else infix(level+1) * terms(level)

  def fromRaw ( s: String ): String = s.replaceAllLiterally("""\n""","\n")
        
  def expr: Parser[Expr]
      = infix(0) | conses

  def sem: Parser[Option[String]] = opt( ";" )

  def char: Parser[String]
      = accept("char literal",{ case t: lexical.CharLit => t.chars })

  def int: Parser[Int]
      = numericLit ^^ { _.toInt }

  def long: Parser[Long]
      = accept("long literal",{ case t: lexical.LongLit => t.chars.init.toLong })

  def double: Parser[Double]
      = accept("double literal",{ case t: lexical.DoubleLit => t.chars.toDouble })

  def conses: Parser[Expr]      /* :: is treated specially: right associative, flips operands */
      = rep1sep( matches, "::" ) ^^
        { es => es.init.foldRight(es.last)
                  { case (e,r) => MethodCall(r,"::",List(e)) } }

  def matches: Parser[Expr]
      = factor ~ rep( "match" ~ "{" ~ rep1sep( "case" ~ pat ~ opt( "by" ~> expr ) ~ "=>" ~ expr, sem ) ~ "}" ) ^^
        { case a~as
            => as.foldLeft(a){ case (r,_~_~cs~_)
                                 => MatchE(r,cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                                     case _~p~_~_~b => Case(p,BoolConst(true),b) }) } }

  def factor: Parser[Expr]
      = term ~ rep( opt( "." ) ~ ident ~ opt( "(" ~> repsep( expr, "," ) <~ ")"
                                            | expr ^^ { (x:Expr) => List(x) } ) ) ^^
        { case a~as => as.foldLeft(a){ case (r,_~n~Some(xs)) => MethodCall(r,n,xs)
                                       case (r,_~n~_) => MethodCall(r,n,null) } }

  def compr: Parser[Comprehension]
    = "[" ~ expr ~ "|" ~ repsep( qual, "," ) ~ "]" ^^
      { case _~e~_~qs~_ => Comprehension(e,qs) }

  def term: Parser[Expr]
      = ( compr
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ~ opt( compr ) ^^
          { case n~_~el~_~Some(c) => Call(n,List(Tuple(el),c))
            case n~_~es~_~None => Call(n,es) }
        | "if" ~ "(" ~ expr ~ ")" ~ expr ~ "else" ~ expr ^^
          { case _~_~p~_~t~_~e => IfE(p,t,e) }
        | "new" ~> ident ~ opt( "(" ~> repsep( expr, "," ) <~ ")" ) ^^
          { case n~Some(es) => Constructor(n,es)
            case n~_ => Constructor(n,Nil) }
        | "true" ^^^ { BoolConst(true) }
        | "false" ^^^ { BoolConst(false) }
        | ( "-" | "+" | "!" ) ~ expr ^^
          { case o~e => MethodCall(e,"unary_"+o,null) }
        | allInfixOpr ~ "/" ~ factor ^^
          { case op~_~e => reduce(op,e) }
        | "{" ~> rep1sep( "case" ~ pat ~ opt( "by" ~> expr ) ~ "=>" ~ expr, sem ) <~ "}" ^^
          { cs => { val nv = AST.newvar
                    Lambda(VarPat(nv),
                           MatchE(Var(nv),
                                  cs.map{ case _~p~Some(c)~_~b => Case(p,c,b)
                                          case _~p~_~_~b => Case(p,BoolConst(true),b) })) } }
        | "(" ~ repsep( pat, "," ) ~ ")" ~ "=>" ~ expr ^^
          { case _~ps~_~_~b => Lambda(TuplePat(ps),b) }
        | ident ~ "=>" ~ expr ^^
          { case v~_~b => Lambda(VarPat(v),b) }
        | ident ~ "[" ~ repsep( expr, "," ) ~ "]"
          ^^ { case v~_~List(e)~_ => Tuple(List(e,Var(v)))
               case v~_~es~_ => Tuple(List(Tuple(es),Var(v))) }
        | "(" ~ expr ~ ")" ~ "[" ~ repsep( expr, "," ) ~ "]"
          ^^ { case _~e~_~_~List(k)~_ => Tuple(List(k,e))
               case _~e~_~_~es~_ => Tuple(List(Tuple(es),e)) }
        | "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case _~es~_ => if (es.length==1) es.head else Tuple(es) }
        | double ^^
          { s => DoubleConst(s) }
        | long ^^
          { s => LongConst(s) }
        | int ^^
          { s => IntConst(s) }
        | stringLit ^^
          { s => StringConst(fromRaw(s)) }
        | char ^^
          { s => CharConst(fromRaw(s).apply(1)) }
        | ident ^^
          { s => Var(s) }
        | failure("illegal start of expression")
        )

  def qual: Parser[Qualifier]
      = ( "group" ~ "by" ~ pat ~ opt( ":" ~ expr ) ^^
          { case _~_~p~Some(_~e) => GroupByQual(p,e)
            case _~_~p~None => GroupByQual(p,AST.toExpr(p)) }
        | pat ~ ("<-" | "=") ~ expr ^^
          { case p~"<-"~e => Generator(p,e)
            case p~"="~e => LetBinding(p,e) }
        | expr ^^ Predicate
        | failure("illegal start of qualifier")
        )

  def pat: Parser[Pattern]
      = spat ~ rep( ( ident | infixOpr | "::" ) ~ spat ) ^^
        { case p~ps => ps.foldLeft(p){ case (r,op~np) => MethodCallPat(r,op,List(np)) } }
  def spat: Parser[Pattern]
      = ( "(" ~ repsep( pat, "," ) ~ ")"
          ^^ { case _~ps~_ => if (ps.length==1) ps.head else TuplePat(ps) }
        | ident ~ "(" ~ repsep( pat, "," ) ~ opt( "*" ) <~ ")" ^^
          { case n~_~(ps:+NamedPat(a,StarPat()))~Some(_) => CallPat(n,ps:+RestPat(a))
            case n~_~(ps:+StarPat())~Some(_) => CallPat(n,ps:+RestPat("_"))
            case _~_~_~Some(_) => throw new Exception("Wrong star pattern")
            case n~_~ps~_ => CallPat(n,ps) }
        | ident ~ "[" ~ repsep( pat, "," ) ~ "]"
          ^^ { case v~_~List(p)~_ => TuplePat(List(p,VarPat(v)))
               case v~_~ps~_ => TuplePat(List(TuplePat(ps),VarPat(v))) }
        | "true" ^^^ { BooleanPat(true) }
        | "false" ^^^ { BooleanPat(false) }
        | ident ~ "@" ~ pat
          ^^ { case n~_~p => if (n=="_") p else NamedPat(n,p) }
        | "_"
          ^^^ { StarPat() }
        | ident
          ^^ { s => if (s == "_") StarPat() else VarPat(s) }
        | double ^^
          { s => DoublePat(s) }
        | long ^^
          { s => LongPat(s) }
        | int ^^
          { s => IntPat(s) }
        | stringLit ^^
          { s => StringPat(fromRaw(s)) }
        | char ^^
          { s => CharPat(fromRaw(s).apply(1)) }
        | failure("illegal start of pattern")
        )

  def pexpr: Parser[Expr]
      = positioned(expr)

  def parse ( line: String ): Expr = {
      queryText = line
      phrase(pexpr)(new lexical.Scanner(line)) match {
          case Success(e,_) => e:Expr
          case m => println(m); Tuple(Nil)
      }
  }

  def main ( args: Array[String] ) {
    println("input : "+ args(0))
    println(Pretty.print(parse(args(0)).toString))
  }
}
