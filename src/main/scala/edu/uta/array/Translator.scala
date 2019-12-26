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

object Translator {
  import AST._

  val arrayClassName = "Array"

  def comprVars ( qs: List[Qualifier] ): List[String]
    = qs.flatMap {
        case Generator(p,_) => patvars(p)
        case LetBinding(p,_) => patvars(p)
        case GroupByQual(p,_) => patvars(p)
        case _ => Nil
      }

  /** Translate a sequence of query qualifiers to an expression */  
  def translateQualifiers ( result: Expr, qs: List[Qualifier] ): Expr =
    qs match {
      case Nil
        => Sequence(List(translate(result)))
      case Generator(p,e)::ns
        => val te = translate(e)
           val ne = translateQualifiers(result,ns)
           flatMap(Lambda(p,ne),te)
      case LetBinding(VarPat(v),e)::ns
        => val te = translateQualifiers(result,ns)
           if (AST.occurrences(v,te) > 1)
              MatchE(translate(e),
                     List(Case(VarPat(v),BoolConst(true),te)))
           else AST.subst(v,translate(e),te)
      case LetBinding(p,e)::ns
        => MatchE(translate(e),
                  List(Case(p,BoolConst(true),
                            translateQualifiers(result,ns))))
      case Predicate(Comprehension(_,s))::ns
        => Block(List(translateQualifiers(s),
                      translateQualifiers(result,ns)))
      case Predicate(e)::ns
        => translateQualifiers(IfE(translate(e),result,Sequence(Nil)),ns)
      case VarDef(v,e)::ns
        => Block(List(VarDecl(v,translate(e)),
                      translateQualifiers(result,ns)))
      case AssignQual(d,e)::ns
        => Block(List(MethodCall(translate(d),"=",List(translate(e))),
                      translateQualifiers(result,ns)))
      case q::_ => throw new Error("Unrecognized qualifier: "+q)
    }

  /** Translate a sequence of query qualifiers to an expression */
  def translateQualifiers ( qs: List[Qualifier] ): Expr =
    qs match {
      case Nil
        => Block(Nil)
      case Generator(p,e)::ns
        => val te = translate(e)
           val ne = translateQualifiers(ns)
           Call("foreach",List(Lambda(p,ne),te))
      case LetBinding(VarPat(v),e)::ns
        => val te = translateQualifiers(ns)
           if (AST.occurrences(v,te) > 1)
              MatchE(translate(e),
                     List(Case(VarPat(v),BoolConst(true),te)))
           else AST.subst(v,translate(e),te)
      case LetBinding(p,e)::ns
        => MatchE(translate(e),
                  List(Case(p,BoolConst(true),
                            translateQualifiers(ns))))
      case Predicate(Comprehension(_,s))::ns
        => Block(List(translateQualifiers(s),
                      translateQualifiers(ns)))
      case Predicate(e)::ns
        => IfE(translate(e),translateQualifiers(ns),Block(Nil))
      case VarDef(v,e)::ns
        => Block(List(VarDecl(v,translate(e)),
                      translateQualifiers(ns)))
      case AssignQual(d,e)::ns
        => Block(List(MethodCall(translate(d),"=",List(translate(e))),
                      translateQualifiers(ns)))
      case q::_ => throw new Error("Unrecognized qualifier: "+q)
    }

  /** Translate comprehensions to the algebra */
  def translate ( e: Expr ): Expr =
    e match {
      case Comprehension(result,qs)
        => qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val liftedVars = freevars(Comprehension(result,s),groupByVars)
                                         .intersect(comprVars(r))
                   val lp = liftedVars match {
                              case List(v)
                                => VarPat(v)
                              case _
                                => TuplePat(liftedVars.map(VarPat))
                            }
                   val vs = newvar
                   def lift ( x: Expr ): Expr
                     = liftedVars.foldRight(x) {
                         case (v,r) => AST.subst(v,flatMap(Lambda(lp,Sequence(List(Var(v)))),
                                                           Var(vs)),
                                                 r) }
                   val re = translate(lift(Comprehension(result,s)))
                   val nh = Tuple(List(k,Tuple(liftedVars.map(Var))))
                   flatMap(Lambda(TuplePat(List(p,VarPat(vs))),re),
                           groupBy(translateQualifiers(nh,r)))
              case _ => result match {
                          case Block(Nil)
                            => translateQualifiers(qs)
                          case _ => translateQualifiers(result,qs)
                        }
           }
      case _ => apply(e,translate)
    }
  }
