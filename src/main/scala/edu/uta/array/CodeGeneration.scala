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

import scala.reflect.macros.whitebox.Context
import scala.reflect.macros.TypecheckException
import scala.language.experimental.macros
import java.io._


abstract class CodeGeneration {
  val c: Context
  import c.universe.{Expr=>_,Block=>_,Apply=>_,_}
  import AST._

  var line: Int = 0

  /** contains bindings from patterns to Scala types */
  type Environment = Map[c.Tree,c.Tree]

  /** add a new binding from a pattern to a Scala type in the Environment */
  def add ( p: Pattern, tp: c.Tree, env: Environment ): Environment =
    env + ((code(p),tp))

  val char_maps = Map( '+' -> "plus", '-' -> "minus", '*' -> "times", '/' -> "div", '%' -> "percent",
                       '|' -> "bar", '&' -> "amp", '!' -> "bang", '^' -> "up", '~' -> "tilde",
                       '=' -> "eq", '<' -> "less", '>' -> "greater", ':' -> "colon", '?' -> "qmark",
                       '\\' -> "bslash" )

  /** Scala translates special chars in method names to $names */
  def method_name ( n: String ): String =
    n.foldLeft(""){ case (r,d) => r+(char_maps.get(d) match { case Some(s) => '$'+s; case _ => d }) }

  /** Return the range type of functionals */
  def returned_type ( tp: c.Tree ): c.Tree = {
    tp match {
       case tq"$d => $r"
         => returned_type(r)
       case _ => tp
    }
  }
  
  /** convert a Type to a Tree. There must be a better way to do this */
  def type2tree ( tp: c.Type ): c.Tree = {
    val ntp = if (tp <:< c.typeOf[AnyVal]) tp.toString.split('(')(0) else tp
    val Typed(_,etp) = c.parse("x:("+ntp+")")
    etp
  }

  def Tree2Type ( tp: c.Tree ): edu.uta.array.Type =
    tp match {
      case tq"(..$cs)" if cs.length > 1
        => TupleType(cs.map(Tree2Type))
      case tq"$n[..$cs]" if cs.nonEmpty
        => ParametricType(n.toString,cs.map(Tree2Type))
      case _
        => BasicType(tp.toString)
    }

  /** Return the type of Scala code, if exists
   *  @param code Scala code
   *  @param env an environment that maps patterns to types
   *  @return the type of code, if the code is typechecked without errors
   */
  def getOptionalType ( code: c.Tree, env: Environment ): Either[c.Tree,TypecheckException] = {
    val cc = var_decls.foldLeft(code){ case (r,(v,vt))
                                         => val vc = TermName(v)
                                            q"($vc:$vt) => $r" }
    val fc = env.foldLeft(cc){ case (r,(p,tq"Any"))
                                 => q"{ case $p => $r }"
                               case (r,(p,tp))
                                 => val nv = TermName(c.freshName("x"))
                                    q"($nv:$tp) => $nv match { case $p => $r }" }
    val te = try c.Expr[Any](c.typecheck(q"{ import edu.uta.array._; $fc }")).actualType
             catch { case ex: TypecheckException => return Right(ex) }
    Left(returned_type(type2tree(te)))
  }

  /** Return the type of Scala code
   *  @param code Scala code
   *  @param env an environment that maps patterns to types
   *  @return the type of code
   */
  def getType ( code: c.Tree, env: Environment ): c.Tree = {
    getOptionalType(code,env) match {
      case Left(tp) => tp
      case Right(ex)
        => println(s"Typechecking error at line $line: ${ex.msg}")
           println("Code: "+code)
           println("Var Decls: "+var_decls)
           println("Bindings: "+env)
           val sw = new StringWriter
           ex.printStackTrace(new PrintWriter(sw))
           println(sw.toString)
           c.abort(c.universe.NoPosition,s"Typechecking error at line $line: ${ex.msg}")
    }
  }

  /** Typecheck the query using the Scala's typechecker */
  def typecheck ( e: Expr, env: Environment = Map() ): c.Tree
    = getType(codeGen(e,env),env)

  /** Typecheck the query using the Scala's typechecker */
  def typecheckOpt ( e: Expr, env: Environment = Map() ): Option[c.Tree]
    = getOptionalType(codeGen(e,env),env) match {
        case Left(tp) => Some(tp)
        case _ => None
    }

  /** For a collection ec, return the element type */
  def typedCodeOpt ( ec: c.Tree, env: Environment ): Option[c.Tree]
    = getOptionalType(ec,env) match {
        case Left(atp)
          => try {
                val ctp = c.Expr[Any](c.typecheck(q"(x:$atp) => x.head")).actualType
                Some(returned_type(type2tree(ctp)))
             } catch { case ex: TypecheckException => return None }
        case Right(_) => None
      }

  /** For a collection e, return the element type and the code of e */
  def typedCode ( e: Expr, env: Environment ): (c.Tree,c.Tree) = {
    val ec = codeGen(e,env)
    typedCodeOpt(ec,env) match {
      case Some(v) => (v,ec)
      case _ => c.abort(c.universe.NoPosition,
                        s"Expression $ec is not a collection (line $line)")
    }
  }

  /** Translate a Pattern to a Scala pattern */
  def code ( p: Pattern ): c.Tree = {
    import c.universe._
    p match {
      case TuplePat(ps)
        => val psc = ps.map(code)
           pq"(..$psc)"
      case NamedPat(n,np)
        => val pc = code(np)
           val nc = TermName(n)
           pq"$nc@$pc"
      case CallPat(n,ps:+RestPat(v))
        => val psc = ps.map(code)
           val f = TermName(method_name(n))
           val tv = TermName(v)
           if (v=="_") pq"$f(..$psc,_*)"
              else pq"$f(..$psc,$tv@_*)"
      case CallPat(n,ps)
        => val psc = ps.map(code)
           val f = TermName(method_name(n))
           pq"$f(..$psc)"
      case MethodCallPat(np,m,ps:+RestPat(v))
        => val pc = code(np)
           val psc = ps.map(code)
           val f = TermName(method_name(m))
           val tv = TermName(v)
           if (v=="_") pq"$f($pc,..$psc,_*)"
              else pq"$f($pc,..$psc,$tv@_*)"
      case MethodCallPat(np,m,ps)
        => val pc = code(np)
           val psc = ps.map(code)
           val f = TermName(method_name(m))
           pq"$f($pc,..$psc)"
      case StringPat(s)
        => pq"$s"
      case CharPat(s)
        => pq"$s"
      case LongPat(n)
        => pq"$n"
      case IntPat(n)
        => pq"$n"
      case DoublePat(n)
        => pq"$n"
      case BooleanPat(n)
        => pq"$n"
      case VarPat(v)
        => val tv = TermName(v)
           pq"$tv"
      case _ => pq"_"
    }
  }

  /** Is this pattern irrefutable (always matches)? */
  def irrefutable ( p: Pattern ): Boolean =
    p match {
      case CallPat(_,_) | MethodCallPat(_,_,_) | StringPat(_) | IntPat(_)
         | LongPat(_) | DoublePat(_) | BooleanPat(_) => false
      case _ => accumulatePat[Boolean](p,irrefutable,_&&_,true)
    }

  /** Eta expansion for method and constructor argument list to remove the placeholder syntax
   *  e.g., _+_ is expanded to (x,y) => x+y
   */
  def codeList ( es: List[Expr], f: List[c.Tree] => c.Tree, env: Environment ): c.Tree = {
    val n = es.map{ case Var("_") => 1; case _ => 0 }.sum
    if (n == 0)
       return f(es.map(codeGen(_,env)))
    val ns = es.map{ case Var("_") => val nv = TermName(c.freshName("x"))
                                      (nv,q"$nv":c.Tree)
                     case e => (null,codeGen(e,env)) }
    val tpt = tq""  // empty type
    val vs = ns.flatMap{ case (null,_) => Nil; case (v,_) => List(q"val $v: $tpt") }
    val ne = f(ns.map(_._2))
    q"(..$vs) => $ne"
  }

  private var var_decls = collection.mutable.Map[String,c.Tree]()

  def element_type ( tp: c.Tree ): c.Tree
    = tp match {
        case tq"Array[$atp]"
          => element_type(atp)
        case _ => tp
      }

  def set_element_type ( tp: c.Tree, etp: c.Tree ): c.Tree
    = tp match {
        case tq"Array[$atp]"
          => val ntp = set_element_type(atp,etp)
             tq"Array[$ntp]"
        case _ => etp
      }

  def mapAccess ( x: Expr, i: Expr, env: Environment ): c.Tree = {
    val xc = codeGen(x,env)
    val ic = codeGen(i,env)
    (getType(xc,env),ic,getType(ic,env)) match {
      case (tq"edu.uta.array.Matrix",q"($i,$j)",_)
        => q"$xc($i,$j)"
      case (tq"Array[$t]",q"(..$is)",_)
        => is.foldLeft[c.Tree](xc) { case (r,n) => q"$r($n)" }
      case (tq"Array[$t]",_,tq"(..$its)")
        if its.length > 1
        => val as = (1 to its.length).foldLeft[c.Tree](xc) {
                          case (r,n) => val v = TermName("_"+n); q"$r(k.$v)"
                    }
           q"{ val k = $ic; $as }"
      case _ => q"$xc($ic)"
    }
  }

  /** Generate Scala code for Traversable (in-memory) collections */
  def codeGen ( e: Expr, env: Environment ): c.Tree = {
    e match {
      case flatMap(Lambda(p,Sequence(List(b))),x)
        if toExpr(p) == b
        => codeGen(x,env)
      case flatMap(Lambda(p,Sequence(List(b))),x)
        if irrefutable(p)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.map(($nv:$tp) => $nv match { case $pc => $bc })"
      case flatMap(Lambda(p,b),x)
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           if (irrefutable(p))
              q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc })"
           else q"$xc.flatMap(($nv:$tp) => $nv match { case $pc => $bc; case _ => Nil })"
      case Call("foreach",List(Lambda(p@VarPat(v),b),x))
        => val (tp,xc) = typedCode(x,env)
           val nv = TermName(v)
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.foreach(($nv:$tp) => $bc)"
      case Call("foreach",List(Lambda(p,b),x))
        => val pc = code(p)
           val (tp,xc) = typedCode(x,env)
           val nv = TermName(c.freshName("x"))
           val bc = codeGen(b,add(p,tp,env))
           q"$xc.foreach(($nv:$tp) => $nv match { case $pc => $bc })"
      case groupBy(x)
        => val xc = codeGen(x,env)
           q"$xc.groupBy(_._1).mapValues( _.map(_._2))"
      case reduce(m,x)
        => val xc = codeGen(x,env)
           val fnc = TermName(method_name(m))
           q"$xc.reduce(_ $fnc _)"
      case Nth(x,n)
        => val xc = codeGen(x,env)
           val nc = TermName("_"+n)
           q"$xc.$nc"
      case Tuple(es)
        => codeList(es,cs => q"(..$cs)",env)
      case Call("Map",Nil)
        => q"scala.collection.mutable.Map[Any,Any]()"
      case Call("Array",d)
        => val dc = d.map(codeGen(_,env))
           q"Array.ofDim[Any](..$dc)"
      case Call(n,es)
        => val fm = TermName(method_name(n))
           codeList(es,cs => q"$fm(..$cs)",env)
      case Constructor(n,es)
        => val fm = TypeName(n)
           codeList(es,cs => q"new $fm(..$cs)",env)
      case MethodCall(Var("_"),m,null)
        => val nv = TermName(c.freshName("x"))
           val fm = TermName(method_name(m))
           val tpt = tq""  // empty type
           val p = q"val $nv: $tpt"
           q"($p) => $nv.$fm"
      case MethodCall(x,m,null)
        if m.length == 1 && char_maps.contains(m(0))
        => val xc = codeGen(x,env)
           val fm = TermName("unary_"+method_name(m))
           q"$xc.$fm"
      case MethodCall(x,m,null)
        => val xc = codeGen(x,env)
           val fm = TermName(method_name(m))
           q"$xc.$fm"
      case MethodCall(x@MapAccess(Var(v),k),"=",List(y))
        => val yc = codeGen(y,env)
           val ty = getType(yc,env)
           getType(codeGen(Var(v),env),env) match {
             case tq"scala.collection.mutable.Map[Any,Any]"
               => val tk = typecheck(k,env)
                  var_decls += ((v,tq"Map[$tk,$ty]"))
             case tp
               => element_type(tp) match {
                     case tq"Any"
                       => var_decls += ((v,set_element_type(tp,ty)))
                     case _ => ;
                  }
           }
           val xc = codeGen(x,env)   // must be last
           q"$xc = $yc"
      case MethodCall(Tuple(xs),"=",List(y))
        => val yc = codeGen(y,env)  // y must be first to setup var_decls
           val v = TermName(c.freshName("x"))
           val xc = xs.zipWithIndex.map {
                      case (x,n)
                        => val xc = codeGen(x,env)
                           val nc = TermName("_"+(n+1))
                           q"$xc = $v.$nc"
                   }
           q"{ val $v = $yc; ..$xc }"
      case MethodCall(x,"=",List(y))
        => val yc = codeGen(y,env)  // y must be first to setup var_decls
           val xc = codeGen(x,env)
           q"$xc = $yc"
      case MethodCall(x@MapAccess(Var(v),k),m,List(y))
        => val z = if (m==":+") Sequence(List(y)) else y
           val yc = codeGen(y,env)
           getType(codeGen(Var(v),env),env) match {
             case tq"scala.collection.mutable.Map[Any,Any]"
               => val tk = typecheck(k,env)
                  val tz = typecheck(z,env)
                  var_decls += ((v,tq"Map[$tk,$tz]"))
             case tp
               => element_type(tp) match {
                     case tq"Any"
                       => var_decls += ((v,set_element_type(tp,typecheck(z,env))))
                     case _ => ;
                  }
           }
           val xc = codeGen(x,env)   // must be last
           val fm = TermName(method_name(m))
           q"$xc.$fm($yc)"
      case Apply(f,x)
        => val fc = codeGen(f,env)
           val xc = codeGen(x,env)
           q"$fc($xc)"
      case MethodCall(x,m,es)
        => val fm = TermName(method_name(m))
           codeList(x+:es,{ case cx+:cs => q"$cx.$fm(..$cs)" },env)
      case MapAccess(v,k)
        => mapAccess(v,k,env)
      case Sequence(Nil)
        => q"Nil"
      case Sequence(s)
        => val sc = s.map(codeGen(_,env))
           q"List(..$sc)"
      case Block(s)
        => val nenv = s.foldLeft(env){ case (r,VarDecl(v,u))
                                         => val tv = TermName(v)
                                            r + ((pq"$tv",typecheck(u,r)))
                                       case (r,u) => r }
           val stmts = s.flatMap{ case VarDecl(_,_) => Nil; case x => List(codeGen(x,nenv)) }
           val decls = s.flatMap{ case x@VarDecl(_,_) => List(codeGen(x,nenv)); case x => Nil }
           q"{ ..$decls; ..$stmts }"
      case VarDecl(v,Call("Map",Nil))
        => val vc = TermName(v)
           if (var_decls.contains(v)) {
              val tq"Map[$kt,$vt]" = var_decls(v)
              q"var $vc = collection.mutable.Map[$kt,$vt]()"
           } else q"var $vc = collection.mutable.Map[Any,Any]()"
      case VarDecl(v,Call("Array",d))
        => val vc = TermName(v)
           val dc = d.map(codeGen(_,env))
           val etp = if (var_decls.contains(v)) element_type(var_decls(v)) else tq"Any"
           q"var $vc = Array.ofDim[$etp](..$dc)"
      case VarDecl(v,u)
        => val vc = TermName(v)
           val uc = codeGen(u,env)
           q"var $vc = $uc"
      case IfE(p,x,y)
        => val pc = codeGen(p,env)
           val xc = codeGen(x,env)
           val yc = codeGen(y,env)
           q"if ($pc) $xc else $yc"
      case MatchE(x,List(Case(VarPat(v),BoolConst(true),b)))
        if occurrences(v,b) == 1
        => codeGen(subst(v,x,b),env)
      case MatchE(x,List(Case(p@VarPat(v),BoolConst(true),b)))
        => val xc = codeGen(x,env)
           val pc = TermName(v)
           val tp = getType(xc,env)
           typedCodeOpt(xc,env) match {
                case Some(_)
                  => val nv = Var(v)
                     val bc = codeGen(subst(Var(v),nv,b),add(p,tp,env))
                     return q"{ val $pc:$tp = $xc; $bc }"
                case None =>
           } 
           val bc = codeGen(b,add(p,tp,env))
           q"{ val $pc:$tp = $xc; $bc }"
      case MatchE(x,List(Case(p,BoolConst(true),b)))
        if irrefutable(p)
        => val xc = codeGen(x,env)
           val tp = getType(xc,env)
           val pc = code(p)
           val bc = codeGen(b,add(p,tp,env))
           q"{ val $pc:$tp = $xc; $bc }"
      case MatchE(x,cs)
        => val xc = codeGen(x,env)
           val tp = getType(xc,env)
           val cases = cs.map{ case Case(p,BoolConst(true),b)
                                 => val pc = code(p)
                                    val bc = codeGen(b,add(p,tp,env))
                                    cq"$pc => $bc"
                               case Case(p,n,b)
                                 => val pc = code(p)
                                    val nc = codeGen(n,env)
                                    val bc = codeGen(b,add(p,tp,env))
                                    cq"$pc if $nc => $bc"
                             }
           q"($xc:$tp) match { case ..$cases }"
      case Lambda(p@VarPat(v),b)
        => val tpt = tq""  // empty type
           val vc = TermName(v)
           val bc = codeGen(b,add(p,tpt,env))
           val pp = q"val $vc: $tpt"
           q"($pp) => $bc"
      case Lambda(p,b)
        => val tpt = tq""  // empty type
           val pc = code(p)
           val bc = codeGen(b,add(p,tpt,env))
           q"{ case $pc => $bc }"
      case IntConst(n)
        => q"$n"
      case LongConst(n)
        => q"$n"
      case DoubleConst(n)
        => q"$n"
      case StringConst(s)
        => q"$s"
      case CharConst(s)
        => q"$s"
      case BoolConst(n)
        => q"$n"
      case Var(v)
        => Ident(TermName(v))
      case _ => throw new Exception("Unrecognized AST: "+e)
    }
  }
 }
