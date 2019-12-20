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

object ComprehensionTranslator {
  import AST._

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }

  def findReducedTerms ( e: Expr, vars: List[String] ): List[(String,Expr)]
    = e match {
        case reduce(_,Var(v))
          if vars.contains(v)
          => List((v,e))
        case reduce(_,flatMap(_,Var(v)))
          if vars.contains(v)
          => List((v,e))
        case Var(v)
          if vars.contains(v)
          => List((v,e))
        case _ => accumulate[List[(String,Expr)]](e,findReducedTerms(_,vars),_++_,Nil)
      }

  def translate ( e: Expr ): Expr
    = e match {
      case Var(a)
        => typecheck_var(a) match {
              case Some(ParametricType("Matrix",List(_)))
                => val i = newvar
                   val j = newvar
                   Comprehension(Tuple(List(Tuple(List(Var(i),Var(j))),
                                            MapAccess(Var(a),Tuple(List(Var(i),Var(j)))))),
                      List(Generator(VarPat(i),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(e,"rows",null)))),
                           Generator(VarPat(j),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(MapAccess(Var(a),Var(i)),
                                                                "cols",null))))))
              case Some(ParametricType("Array",List(ParametricType("Array",List(_)))))
                => val i = newvar
                   val j = newvar
                   Comprehension(Tuple(List(Tuple(List(Var(i),Var(j))),
                                            MapAccess(MapAccess(Var(a),Var(i)),Var(j)))),
                      List(Generator(VarPat(i),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(e,"length",null)))),
                           Generator(VarPat(j),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(MapAccess(Var(a),Var(i)),
                                                                "length",null))))))
              case Some(ParametricType("Array",List(_)))
                => val i = newvar
                   Comprehension(Tuple(List(Var(i),MapAccess(Var(a),Var(i)))),
                      List(Generator(VarPat(i),
                                     MethodCall(IntConst(0),"until",
                                                List(MethodCall(e,"length",null))))))
              case _ => Var(a)
           }
      case Comprehension(result,qs)
        => qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(result,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(Comprehension(result,s),usedVars)
                   val reducedTerms = rt.filter{ case (_,reduce(_,_)) => true; case _ => false }
                   val reducedVars = reducedTerms.map(_._1)
                   val liftedVars = rt.filter{ case (_,reduce(_,_)) => false; case _ => true }.map(_._1)
println("@@@ "+reducedTerms+"  "+liftedVars)
                   val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
                   val kv = newvar
                   val vs = newvar
                   val xv = newvar
                   val env = reducedTerms.map{ case (v,t) => (t,MapAccess(Var("_"+v),Var(kv))) } ++
                                     liftedVars.map(v => (Var(v),Comprehension(Var(v),
                                                                     List(Generator(lp,Var(vs))))))
                   val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,to,r) }
                   val Comprehension(nh,ns) = lift(Comprehension(result,s))
                   val init = (if (liftedVars.isEmpty) Nil else List(VarDef(xv,Call("LMap",Nil)))) ++
                                    reducedVars.map(v => VarDef("_"+v,Call("Map",Nil)))
                   val incr = (if (liftedVars.isEmpty) Nil else List(AssignQual(MapAccess(Var(xv),Var(kv)),
                                                IfE(MethodCall(Var(xv),"contains",List(Var(kv))),
                                                    MethodCall(MapAccess(Var(xv),Var(kv)),
                                                               ":+",
                                                               List(le)),
                                                    Sequence(Nil))))) ++
                                    reducedTerms.map {
                                       case (v,reduce(m,e))
                                         => AssignQual(MapAccess(Var("_"+v),Var(kv)),
                                                       MethodCall(MapAccess(Var("_"+v),Var(kv)),
                                                                  m,
                                                                  List(e)))
                                       case _ => Predicate(BoolConst(true))
                                    }
                   val nqs = r++List(LetBinding(VarPat(kv),k))++incr
                   val rv = if (liftedVars.isEmpty)
                               Var("_"+reducedVars.head)
                            else Var(xv)
                   translate(Comprehension(nh,
                                           init
                                           ++ List(Predicate(Comprehension(BoolConst(true),nqs)),
                                                   Generator(TuplePat(List(VarPat(kv),StarPat())),rv),
                                                   LetBinding(p,Var(kv)))
                                           ++ ns))
               case _ => apply(e,translate)
           }
      case _ => apply(e,translate)
    }
}
