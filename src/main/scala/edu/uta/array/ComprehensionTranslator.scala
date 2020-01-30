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

//import edu.uta.array.ComprehensionTranslator.translate

object ComprehensionTranslator {
  import AST._

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }

  def yieldReductions ( e: Expr, vars: List[String] ): Expr
    = e match {
        case MethodCall(Var(v),"length",null)
          if vars.contains(v)
          => reduce("+",MethodCall(Var(v),"map",List(Lambda(VarPat("x"),IntConst(1)))))
        case _ => apply(e,yieldReductions(_,vars))
      }

  def findReducedTerms ( e: Expr, vars: List[String] ): List[(String,Expr)]
    = e match {
        case reduce(_,Var(v))
          if vars.contains(v)
          => List((v,e))
        case reduce(_,flatMap(_,Var(v)))
          if vars.contains(v)
          => List((v,e))
        case reduce(_,MethodCall(Var(v),f,_))
          if List("map","flatMap").contains(f) && vars.contains(v)
          => List((v,e))
        case Var(v)
          if vars.contains(v)
          => List((v,e))
        case _ => accumulate[List[(String,Expr)]](e,findReducedTerms(_,vars),_++_,Nil)
      }

  @scala.annotation.tailrec
  def translate_comprehension(result: List[Expr], qs: List[Qualifier] ): (List[Expr],List[Qualifier]) = {
    qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(result,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(result,s),usedVars),
                                             usedVars)
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                        .map(x => (newvar,x._2))
                   val reducedVars = reducedTerms.map(_._1)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                                      .map(_._1).distinct
                   val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
                   val kv = newvar
                   val xv = newvar
                   val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var(v),Var(kv))) } ++
                                       liftedVars.map(v => (Var(v),Comprehension(List(Var(v)),
                                                   List(Generator(lp,MapAccess(Var(xv),Var(kv)))))))
                   val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
                   val Comprehension(nh,ns) = lift(yieldReductions(Comprehension(result,s),usedVars))
                   val init = (if (liftedVars.isEmpty) Nil else List(VarDef(xv,Call("Map",Nil)))) ++
                                    reducedVars.map(v => VarDef(v,Call("Map",Nil)))
                   val incr = (if (liftedVars.isEmpty) Nil else List(AssignQual(MapAccess(Var(xv),Var(kv)),
                                                IfE(MethodCall(Var(xv),"contains",List(Var(kv))),
                                                    MethodCall(MapAccess(Var(xv),Var(kv)),
                                                               ":+",
                                                               List(le)),
                                                    Sequence(List(le)))))) ++
                                    reducedTerms.map {
                                       case (v,reduce(m,MethodCall(e,"map",List(f))))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                       IfE(MethodCall(Var(v),"contains",List(Var(kv))),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(Apply(f,e))),
                                                           Apply(f,e)))
                                       case (v,reduce(m,e))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                       IfE(MethodCall(Var(v),"contains",List(Var(kv))),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(e)),
                                                           e))
                                       case _ => Predicate(BoolConst(true))
                                    }
                   val nqs = r++List(LetBinding(VarPat(kv),k))++incr
                   val rv = if (liftedVars.isEmpty)
                               Var(reducedVars.head)
                            else Var(xv)
                   translate_comprehension(nh,
                                           init
                                           ++ List(Predicate(Comprehension(List(BoolConst(true)),nqs)),
                                                   Generator(VarPat(kv),MethodCall(rv,"keys",null)),
                                                   LetBinding(p,Var(kv)))
                                           ++ ns)
              case _ => (result,qs)
    }
  }

  def array_generators ( e: Expr, tp: Type ): List[(String,Qualifier)]
    = tp match {
        case ParametricType("Array",List(atp))
          => val i = newvar
             (i -> Generator(VarPat(i),
                       MethodCall(IntConst(0),"until",
                                  List(MethodCall(e,"length",null))))) ::
                   array_generators(MapAccess(e,Var(i)),atp)
        case _ => Nil
      }

  def translate ( e: Expr ): Expr = {
    e match {
      case Var(a)
        => typecheck_var(a) match {
              case Some(BasicType("edu.uta.array.Matrix"))
                => val i = newvar
                   val j = newvar
                   Comprehension(List(Tuple(List(Tuple(List(Var(i),Var(j))),
                                            MapAccess(Var(a),Tuple(List(Var(i),Var(j))))))),
                      List(Generator(VarPat(i),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(e,"rows",null)))),
                           Generator(VarPat(j),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(e,"cols",null))))))
              case Some(tp@ParametricType("Array",_))
                => val gs = array_generators(e,tp)
                   val is = if (gs.length == 1) Var(gs.head._1) else Tuple(gs.map(x => Var(x._1)))
                   val mas = gs.foldLeft[Expr](e){ case (r,(v,_)) => MapAccess(r,Var(v)) }
                   Comprehension(List(Tuple(List(is,mas))),
                                 gs.map(_._2))
              case _ => Var(a)
           }
      case Call(array,List(Tuple(d),Comprehension(List(result@Tuple(List(key,e))),qs:+GroupByQual(p,k))))
        if optimize && key == toExpr(p)
        => val groupByVars = patvars(p)
           val usedVars = freevars(result,groupByVars).intersect(comprVars(qs)).distinct
           val rt = findReducedTerms(yieldReductions(result,usedVars),usedVars)
           val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                                .map(x => (newvar,x._2))
           val reducedVars = reducedTerms.map(_._1)
           val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }
                              .map(_._1).distinct
           val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
           val kv = newvar
           val xv = newvar
           val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var(v),Var(kv))) } ++
                               liftedVars.map(v => (Var(v),Comprehension(List(Var(v)),
                                                      List(Generator(lp,MapAccess(Var(xv),Var(kv)))))))
//println("@@@ "+rt+"     "+reducedTerms+"       "+env)
           val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
           def lift ( x: Expr ): Expr
             = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
           val ne = lift(yieldReductions(e,usedVars))
           val init = (if (liftedVars.isEmpty) Nil else List(VarDecl(xv,Call(array,d)))) ++
                                    reducedVars.map(v => VarDecl(v,Call(array,d)))
           val incr = (if (liftedVars.isEmpty) Nil else List(AssignQual(MapAccess(Var(xv),Var(kv)),
                                                      MethodCall(MapAccess(Var(xv),Var(kv)),
                                                               ":+",
                                                               List(le))))) ++
                                    reducedTerms.map {
                                       case (v,reduce(m,MethodCall(e,"map",List(f))))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(Apply(f,e))))
                                       case (v,reduce(m,e))
                                         => AssignQual(MapAccess(Var(v),Var(kv)),
                                                           MethodCall(MapAccess(Var(v),Var(kv)),
                                                                      m,
                                                                      List(e)))
                                       case _ => Predicate(BoolConst(true))
                                    }
           val nqs = qs++List(LetBinding(VarPat(kv),k))++incr
           ne match {
             case MapAccess(Var(v),Var(k))
               if reducedVars.contains(v) && k == kv
               => translate(Block(init ++ List(Comprehension(Nil,nqs),Var(reducedVars.head))))
             case _
              => val rv = newvar
                 translate(Block(VarDecl(rv,Call(array,d))::init
                              ++ List(Comprehension(Nil,
                                          nqs :+ AssignQual(MapAccess(Var(rv),Var(kv)),ne)),Var(rv))))
           }
      case Call("Array",List(Var(nv),Comprehension(hs,qs)))
        if optimize
        => val (nhs,nqs) = translate_comprehension(hs,qs)
           val kv = newvar
           val v = newvar
           val nr = nqs ++ List(Generator(TuplePat(List(VarPat(kv),VarPat(v))),Sequence(nhs)),
                                AssignQual(MapAccess(Var(nv),Var(kv)),Var(v)))
           translate(Block(List(Comprehension(Nil,nr),Var(nv))))
      case Call(array,List(Tuple(d),Comprehension(hs,qs)))
        if optimize
        => val (nhs,nqs) = translate_comprehension(hs,qs)
           val nv = newvar
           val kv = newvar
           val v = newvar
           val nr = nqs ++ List(Generator(TuplePat(List(VarPat(kv),VarPat(v))),Sequence(nhs)),
                                AssignQual(MapAccess(Var(nv),Var(kv)),Var(v)))
           translate(Block(List(VarDecl(nv,Call(array,d)),
                                Comprehension(Nil,nr),Var(nv))))
      case Call(array,List(Tuple(d),c@Comprehension(_,_)))
        if !optimize
        => val v = newvar
           val is = d.map(_ => newvar)
           translate(Block(List(VarDecl(v,Call(array,d)),
                      Comprehension(Nil,
                            List(Generator(TuplePat(List(TuplePat(is.map(VarPat)),VarPat("v"))),
                                           translate(c)),
                                 AssignQual(MapAccess(Var(v),Tuple(is.map(Var))),Var("v")))),
                      Var(v))))
      case Comprehension(result,qs)
        if optimize
        => val (nh,nqs) = translate_comprehension(result,qs)
           apply(Comprehension(nh,nqs),translate)
      case _ => apply(e,translate)
    }
  }
}
