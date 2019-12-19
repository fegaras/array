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

  def translate ( e: Expr ): Expr
    = e match {
      case Var(a)
        => typecheck_var(a) match {
              case Some(ParametricType("Array",List(ParametricType("Array",List(t)))))
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
              case t => Var(a)
           }
      case Comprehension(result,qs)
        => qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val liftedVars = freevars(Comprehension(result,s),groupByVars)
                                              .intersect(comprVars(r))
                   val le = liftedVars match {
                              case List(v)
                                => Var(v)
                              case _
                                => Tuple(liftedVars.map(Var))
                            }
                   val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
                   val vs = newvar
                   def lift ( x: Expr ): Expr
                     = liftedVars.foldRight(x) {
                         case (v,r) => AST.subst(v,Comprehension(Var(v),
                                                           List(Generator(lp,Var(vs)))),
                                                 r) }
                   val Comprehension(nr,ns) = lift(Comprehension(result,s))
                   val kv = newvar
                   val xv = newvar
                   val nqs = r++List(LetBinding(VarPat(kv),k),
                                     AssignQual(MapAccess(Var(xv),Var(kv)),
                                                IfE(MethodCall(Var(xv),"contains",List(Var(kv))),
                                                    MethodCall(MapAccess(Var(xv),Var(kv)),
                                                               ":+",
                                                               List(le)),
                                                    Sequence(Nil))))
                   translate(Comprehension(nr,
                                 List(VarDef(xv,Call("LMap",Nil)),
                                      Predicate(Comprehension(BoolConst(true),
                                                              nqs)),
                                      Generator(TuplePat(List(p,VarPat(vs))),Var(xv)))
                                 ++ns))
              case _ => apply(e,translate(_))
        }
      case _ => apply(e,translate(_))
    }

}
