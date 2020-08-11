/*
 * Copyright © 2020 University of Texas at Arlington
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


abstract class Lifting extends CodeGeneration {
  import AST._

  val TileType = "Array"
  val RDDType = "org.apache.spark.rdd.RDD"
  val MatrixType = "edu.uta.array.Matrix"

  def typed_lift ( e: Expr, tp: Type ): (String,Type,Expr)
    = tp match {
        case BasicType(MatrixType)
          => ( "matrix",
               ParametricType("List",
                              List(TupleType(List(TupleType(List(BasicType("Int"),
                                                                 BasicType("Int"))),
                                                  BasicType("Double"))))),
               { val i = newvar
                 val j = newvar
                 val v = newvar
                 Comprehension(List(Tuple(List(Tuple(List(Var(i),Var(j))),
                                               MapAccess(Var(v),Tuple(List(Var(i),Var(j))))))),
                               List(LetBinding(VarPat(v),e),
                                    Generator(VarPat(i),
                                              MethodCall(IntConst(0),"until",
                                                         List(MethodCall(Var(v),"rows",null)))),
                                    Generator(VarPat(j),
                                              MethodCall(IntConst(0),"until",
                                                         List(MethodCall(Var(v),"cols",null))))))
               } )
        case ParametricType("Array",List(_))
          => ( "array",
               { def sparsifier_type ( tp: Type ): (Int,Type)
                   = tp match {
                       case ParametricType("Array",List(atp))
                         => val (n,etp) = sparsifier_type(atp)
                            (n+1,etp)
                       case _ => (0,tp)
                     }
                 val (n,etp) = sparsifier_type(tp)
                 val ttp = if (n < 2)
                             BasicType("Int")
                           else TupleType((0 until n).toList.map{ i => BasicType("Int") })
                 ParametricType("List",List(TupleType(List(ttp,etp))))
               },
               { def array_generators ( e: Expr, tp: Type ): List[(String,Qualifier)]
                   = tp match {
                       case ParametricType("Array",List(atp))
                         => val i = newvar
                            (i -> Generator(VarPat(i),
                                            MethodCall(IntConst(0),"until",
                                                       List(MethodCall(e,"length",null))))) ::
                                                         array_generators(MapAccess(e,Var(i)),atp)
                       case _ => Nil
                     }
                 val gs = array_generators(e,tp)
                 val is = if (gs.length == 1) Var(gs.head._1) else Tuple(gs.map(x => Var(x._1)))
                 val mas = gs.foldLeft[Expr](e){ case (r,(w,_)) => MapAccess(r,Var(w)) }
                 Comprehension(List(Tuple(List(is,mas))),
                               gs.map(_._2))
               } )
        case ParametricType(TileType,List(etp))
          => ( "tile",
               ParametricType("List",
                              List(TupleType(List(TupleType(List(BasicType("Int"),
                                                                 BasicType("Int"))),
                                                  etp)))),
               { val i = newvar
                 val j = newvar
                 val gs = List(i -> Generator(VarPat(i),
                                              MethodCall(IntConst(0),"until",
                                                         List(IntConst(tileSize)))),
                               j -> Generator(VarPat(j),
                                              MethodCall(IntConst(0),"until",
                                                         List(IntConst(tileSize)))))
                 val is = Tuple(gs.map(x => Var(x._1)))
                 val mas = MapAccess(e,MethodCall(MethodCall(Var(i),"*",List(IntConst(tileSize))),
                                                  "+",List(Var(j))))
                 Comprehension(List(Tuple(List(is,mas))),
                               gs.map(_._2))
               } )
        case TupleType(List(BasicType("Int"),BasicType("Int"),
                            ParametricType(RDDType,
                                           List(TupleType(List(TupleType(List(BasicType("Int"),
                                                                              BasicType("Int"))),
                                                               ParametricType(TileType,List(etp))))))))
          => ( "tiled",
               ParametricType("List",
                              List(TupleType(List(TupleType(List(BasicType("Int"),
                                                                 BasicType("Int"))),
                                                  etp)))),
               { val ii = newvar; val jj = newvar
                 val a = newvar; val v = newvar
                 val i = newvar; val j = newvar
                 val n = newvar; val m = newvar
                 val N = IntConst(tileSize)
                 Comprehension(List(Tuple(List(Tuple(List(Var(i),Var(j))),
                                               MapAccess(Var(v),
                                                         Tuple(List(MethodCall(Var(i),"%",List(N)),
                                                                    MethodCall(Var(j),"%",List(N)))))))),
                               List(LetBinding(TuplePat(List(VarPat(n),VarPat(m),VarPat(a))),e),
                                    Generator(TuplePat(List(TuplePat(List(VarPat(ii),VarPat(jj))),
                                                            VarPat(v))),
                                              Call("lifted",List(StringConst("rdd"),Var(a),Var(a)))),
                                    Generator(VarPat(i),
                                              MethodCall(IntConst(0),"until",List(Var(n)))),
                                    Generator(VarPat(j),
                                              MethodCall(IntConst(0),"until",List(Var(m)))),
                                    Predicate(MethodCall(Var(ii),"==",List(MethodCall(Var(i),"/",List(N))))),
                                    Predicate(MethodCall(Var(jj),"==",List(MethodCall(Var(j),"/",List(N)))))))
               } )
        case ParametricType(RDDType,List(etp))
          => ( "rdd",
               ParametricType("List",List(etp)),
               e )
        case BasicType("scala.collection.immutable.Range.Inclusive")
          => ( "range",
               ParametricType("List",List(BasicType("Int"))),
               e )
        case _ => println("$$$$ "+tp);("none",tp,e)
     }

  def lift_domain ( e: Expr, tp: Type ): (Expr,Type)
    = typed_lift(e,tp) match {
        case ("none",t,_)
          => (e,t)
        case (n,t,x)
          => (Call("lifted",List(StringConst(n),x,e)),t)
      }

  def lift ( qs: List[Qualifier], env: Environment ): (List[Qualifier],Environment)
    = qs.foldLeft[(List[Qualifier],Environment)]((Nil,env)){
           case ((r,n),q@Generator(p,e))
             => val tp = typecheck(e,n)
                lift_domain(lift(e,n),Tree2Type(tp)) match {
                   case (lifted,ParametricType(_,List(ltp)))
                     => ( r:+Generator(p,lifted), add(p,Type2Tree(ltp),n) )
                   case _ => (r:+apply(q,(x:Expr)=>lift(x,n)),n)
                }
           case ((r,n),LetBinding(p,e))
             => val tp = typecheck(e,n)
                ( r:+LetBinding(p,lift(e,n)), add(p,tp,n) )
           case ((r,n),GroupByQual(p,e))
             => val tp = typecheck(e,n)
                ( r:+GroupByQual(p,lift(e,n)), add(p,tp,n) )
           case ((r,n),q)
             => (r:+apply(q,(x:Expr)=>lift(x,n)),n)
      }

  def lift ( e: Expr, env: Environment ): Expr
    = e match {
        case Comprehension(hds,qs)
          => val (nqs,nenv) = lift(qs,env)
             Comprehension(hds.map(x => lift(x,nenv)),nqs)
        case flatMap(Lambda(p,b),x)
          => val (tp,xc) = typedCode(x,env)
             flatMap(Lambda(p,lift(b,add(p,tp,env))),
                     lift(x,env))
        case Call("array",List(Lambda(p,x),z))
          => val tp = typecheck(z,env)
             val nx = lift(x,add(p,tp,env))
             Call("array",List(Lambda(p,nx),lift(z,env)))
        case MatchE(x,cs)
          => val tp = typecheck(x,env)
             MatchE(lift(x,env),
                    cs.map{ case Case(p,c,b)
                              => Case(p,lift(c,env),
                                      lift(b,add(p,tp,env)))
                          })
        case _ => apply(e,(x:Expr)=>lift(x,env))
    }
}
