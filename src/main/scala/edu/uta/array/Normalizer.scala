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

object Normalizer {
  import AST._

  /** rename the variables in the lambda abstraction to prevent name capture */
  def renameVars ( f: Lambda ): Lambda =
    f match {
      case Lambda(p,b)
        => val m = patvars(p).map((_,newvar))
           Lambda(m.foldLeft(p){ case (r,(from,to)) => subst(from,to,r) },
                  m.foldLeft(b){ case (r,(from,to)) => subst(from,Var(to),r) })
    }

  def isSimple ( e: Expr ): Boolean =
    e match {
      case Var(_) => true
      case StringConst(_) => true
      case CharConst(_) => true
      case IntConst(_) => true
      case LongConst(_) => true
      case DoubleConst(_) => true
      case BoolConst(_) => true
      case Nth(u,_)
        => isSimple(u)
      case Tuple(cs)
        => cs.isEmpty || cs.map(isSimple).reduce(_&&_)
      case Sequence(cs)
        => cs.isEmpty || cs.map(isSimple).reduce(_&&_)
      case _ => false
    }

  def freeEnv ( p: Pattern, env: Map[String,Expr] ): Map[String,Expr]
    = env.filter(x => !capture(x._1,p))

  def bindEnv ( p: Pattern, e: Expr ): Map[String,Expr] =
    (p,e) match {
      case (TuplePat(Nil),_)
        => Map()
      case (TuplePat(ps),Tuple(ts))
        => (ps zip ts).map{ case (q,x) => bindEnv(q,x) }.reduce(_++_)
      case (TuplePat(ps),u)
        => ps.zipWithIndex.map{ case (q,i) => bindEnv(q,Nth(u,i+1)) }.reduce(_++_)
      case (VarPat(v),_)
        => Map(v->e)
      case _ => Map()
    }

  def substE ( e: Expr, env: Map[String,Expr] ): Expr
    = env.foldLeft[Expr](e) { case (r,(v,u)) => subst(v,u,r) }

  def substP ( p: Pattern, env: Map[String,String] ): Pattern
    = p match {
        case VarPat(v)
          => if (env.contains(v)) VarPat(env(v)) else p
        case TuplePat(ts)
          => TuplePat(ts.map(substP(_,env)))
        case _ => p
      }

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }

  def canInline ( qs: List[Qualifier] ): Boolean
    = qs.forall{
        case GroupByQual(_,_)
          => false
        case AssignQual(_,_)
          => false
        case _ => true
      }

  @scala.annotation.tailrec
  def canInline ( p: Pattern, hds: Expr, qs: List[Qualifier] ): Boolean
    = qs match {
        case GroupByQual(gp,_)::r
          if p == gp
          => canInline(p,hds,r)
        case GroupByQual(_,_)::r
          => patvars(p).map( s => occurrences(s,Comprehension(List(hds),r)) ).sum == 0
        case _::r => canInline(p,hds,r)
        case Nil => true
      }

  def pure ( e: Expr ): Boolean
    = e match {
        case Call("random",_) => false
        case _ => accumulate[Boolean](e,pure,_&&_,true)
      }

  def renameVars ( hds: List[Expr], qs: List[Qualifier], env: Map[String,String] ): List[Qualifier] = {
    def nenv ( p: Pattern ): Map[String,String]
      = env ++ patvars(p).map(_ -> newvar).toMap
    def subst ( e: Expr ): Expr
      = substE(e,env.mapValues(Var(_)))
    qs match {
      case Nil
        => hds.map(x => Predicate(subst(x)))
      case Generator(p,u)::r
        => val ne = nenv(p)
           Generator(substP(p,ne),subst(u))::renameVars(hds,r,ne)
      case LetBinding(p,u)::r
        => val ne = nenv(p)
           LetBinding(substP(p,ne),subst(u))::renameVars(hds,r,ne)
      case GroupByQual(p,u)::r
        => val ne = nenv(p)
           GroupByQual(substP(p,ne),subst(u))::renameVars(hds,r,ne)
      case VarDef(v,u)::r
        => val ne = nenv(VarPat(v))
           VarDef(ne(v),subst(u))::renameVars(hds,r,ne)
      case Predicate(u)::r
        => Predicate(subst(u))::renameVars(hds,r,env)
      case AssignQual(d,v)::r
        => AssignQual(subst(d),subst(v))::renameVars(hds,r,env)
    }
  }

  def renameVars ( e: Comprehension ): Comprehension
    = e match {
        case Comprehension(hds,qs)
          => val nqs:+Predicate(nhds) = renameVars(hds,qs,Map())
             Comprehension(List(nhds),nqs)
      }

  def empty () = Sequence(Nil)
  def elem ( x: Expr ) = Sequence(List(x))

  /** Normalize a comprehension */
  def normalize ( hds: List[Expr], qs: List[Qualifier], env: Map[String,Expr] ): List[Qualifier] =
    qs match {
      case Nil
        => List(LetBinding(VarPat("@result"),
                           Tuple(hds.map(x => substE(x,env)))))
      case Generator(p,Sequence(List(u)))::r
        => normalize(hds,LetBinding(p,u)::r,env)
      case Generator(_,Sequence(Nil))::_
        => Nil
      case Generator(p,c@Comprehension(List(_),s))::r
        if canInline(s)
        => val Comprehension(List(hd),s) = renameVars(normalize(c).asInstanceOf[Comprehension])
           normalize(hds,(s:+LetBinding(p,hd))++r,env)
      case Generator(p,u)::r
        => Generator(p,normalize(substE(u,env)))::normalize(hds,r,freeEnv(p,env))
      case LetBinding(TuplePat(ps),Tuple(es))::r
        => normalize(hds,(ps zip es).map{ case (p,e) => LetBinding(p,e) }++r,env)
      case LetBinding(p@VarPat(v),u@Var(w))::r
        if pure(u) && canInline(p,Tuple(hds),r)
        => normalize(hds,r,env+(v->substE(Var(w),env)))
      case LetBinding(p,u)::r
        => if (pure(u) && canInline(p,Tuple(hds),r))
              normalize(hds,r,bindEnv(p,normalize(substE(u,env)))++freeEnv(p,env))
           else LetBinding(p,normalize(substE(u,env)))::normalize(hds,r,env)
      case Predicate(BoolConst(false))::_
        => Nil
      case Predicate(BoolConst(true))::r
        => normalize(hds,r,env)
      case Predicate(u)::r
        => Predicate(substE(u,env))::normalize(hds,r,env)
      case GroupByQual(p,u)::r
        => // lift all env vars except the group-by pattern vars
           val nenv = freeEnv(p,env).map{ case (v,x) => (v,elem(x)) }
           GroupByQual(p,normalize(substE(u,env)))::normalize(hds,r,nenv)
      case AssignQual(d,v)::r
        => AssignQual(substE(d,env),substE(v,env))::normalize(hds,r,env)
      case VarDef(v,u)::r
        => VarDef(v,substE(u,env))::normalize(hds,r,env)
    }

  /** normalize an expression */
  def normalize ( e: Expr ): Expr =
    e match {
      case Apply(Lambda(p@VarPat(v),b),u)
        => val nu = normalize(u)
           val nb = normalize(b)
           normalize(if (isSimple(nu) || occurrences(v,nb) <= 1)
                        subst(Var(v),nu,nb)
                     else Let(p,nu,nb))
      case Let(VarPat(v),u,b)
        if isSimple(u) || occurrences(v,b) <= 1
        => normalize(subst(Var(v),u,b))
      case Comprehension(hds,List())
        => Sequence(hds.map(normalize))
      case Comprehension(h,Predicate(p)::qs)
        => IfE(p,Comprehension(h,qs),empty())
/* (needs renaming)
      case Comprehension(h,Generator(p,c@Comprehension(_,_))::qs)
        => val Comprehension(List(h2),s) = renameVars(c)
           normalize(Comprehension(h,(s:+LetBinding(p,h2))++qs))
*/
      case Comprehension(hds,qs)
        => normalize(hds,qs,Map()) match {
             case nqs:+LetBinding(VarPat("@result"),Tuple(nh))
               => val nc = Comprehension(nh,nqs)
                  if (nc == e)
                     apply(nc,normalize)
                  else normalize(nc)
             case _ => empty()
           }
      case reduce(m,Sequence(List(x)))
        => normalize(x)
      case reduce(m,Sequence(Nil))
        => empty()
      case Block(Nil)
        => e
      case Block(l)
        if l.map{ case Block(_) => true; case _ => false }.reduce(_||_)
        => Block(l.flatMap{ case Block(s) => s; case x => List(x) })
      case IfE(BoolConst(true),e1,_)
        => normalize(e1)
      case IfE(BoolConst(false),_,e2)
        => normalize(e2)
      case Call(a,List(Tuple(s)))
        => val pat = """_(\d+)""".r
           a match {
             case pat(x) if x.toInt <= s.length
               => normalize(s(x.toInt-1))
             case _ => Call(a,List(Tuple(s.map(normalize))))
           }
      case Call("!",List(Call("||",List(x,y))))
        => normalize(Call("&&",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("&&",List(x,y))))
        => normalize(Call("||",List(Call("!",List(x)),Call("!",List(y)))))
      case Call("!",List(Call("!",List(x))))
        => normalize(x)
      case Call("!",List(Call("!=",List(x,y))))
        => normalize(Call("==",List(x,y)))
      case Call("&&",List(BoolConst(b),x))
        => if (b) normalize(x) else BoolConst(false)
      case Call("&&",List(x,BoolConst(b)))
        => if (b) normalize(x) else BoolConst(false)
      case Call("||",List(BoolConst(b),x))
        => if (b) BoolConst(true) else normalize(x)
      case Call("||",List(x,BoolConst(b)))
        => if (b) BoolConst(true) else normalize(x)
      case Nth(Tuple(es),n)
        => normalize(es(n-1))
      case _ => apply(e,normalize)
    }

  def normalizeAll ( e: Expr ): Expr = {
    var olde = e
    var ne = olde
    do { olde = ne
         ne = normalize(ne)
       } while (olde != ne)
    ne
  }
}
