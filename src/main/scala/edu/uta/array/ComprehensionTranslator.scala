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

  /* general span for comprehensions; if a qualifier matches, split there and continue with cont */
  def matchQ ( qs: List[Qualifier], filter: Qualifier => Boolean,
               cont: List[Qualifier] => Option[List[Qualifier]] ): Option[List[Qualifier]]
    = qs match {
        case q::r
          if filter(q)
          => cont(qs) match {
               case r@Some(s) => r
               case _ => matchQ(r,filter,cont)
             }
        case _::r
          => matchQ(r,filter,cont)
        case _ => None
      }

  def tuple ( s: List[Expr] ): Expr
    = s match { case List(x) => x; case _ => Tuple(s) }

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
  def translate_groupbys ( nhs: List[Expr], qs: List[Qualifier] ): (List[Expr],List[Qualifier]) = {
    qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(nhs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(nhs,s),usedVars),
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
                   val Comprehension(nh,ns) = lift(yieldReductions(Comprehension(nhs,s),usedVars))
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
                   translate_groupbys(nh,init
                                         ++ List(Predicate(Comprehension(List(BoolConst(true)),nqs)),
                                                 Generator(VarPat(kv),MethodCall(rv,"keys",null)),
                                                 LetBinding(p,Var(kv)))
                                         ++ ns)
              case _ => (nhs,qs)
    }
  }

  def lift_array_expr ( u: Expr, tp: Option[Type] ): Expr
    = tp match {
          case Some(BasicType("edu.uta.array.Matrix"))
            => val i = newvar
               val j = newvar
               Comprehension(List(Tuple(List(Tuple(List(Var(i),Var(j))),
                                        MapAccess(u,Tuple(List(Var(i),Var(j))))))),
                  List(Generator(VarPat(i),
                                 MethodCall(IntConst(0),"until",
                                            List(MethodCall(u,"rows",null)))),
                       Generator(VarPat(j),
                                 MethodCall(IntConst(0),"until",
                                            List(MethodCall(u,"cols",null))))))
          case Some(tp@ParametricType("Array",_))
            => val gs = array_generators(u,tp)
               val is = if (gs.length == 1) Var(gs.head._1) else Tuple(gs.map(x => Var(x._1)))
               val mas = gs.foldLeft[Expr](u){ case (r,(w,_)) => MapAccess(r,Var(w)) }
               Comprehension(List(Tuple(List(is,mas))),
                             gs.map(_._2))
          case _ => u
       }

  def translate_comprehension ( hs: List[Expr], qs: List[Qualifier] ): (List[Expr],List[Qualifier]) = {
    val (nhs,nqs) = translate_groupbys(hs,qs)
    val nqs2 = nqs.map{ case Generator(p,u@Var(v))
                          => Generator(p,lift_array_expr(u,typecheck_var(v)))
                        case x@Generator(p,u)
                          => try {
                               Generator(p,lift_array_expr(u,typecheck_expr(u)))
                          } catch { case _ : Throwable => x }
                        case x => x }
    (nhs,nqs2)
  }

  def isRDD ( e: Expr ): Boolean
    = e match {
        case Var(v)
          => typecheck_var(v) match {
                case Some(ParametricType("org.apache.spark.rdd.RDD",List(_)))
                  => true
                case _ => false
             }
        case _
          => try {
                typecheck_expr(e) match {
                  case Some(ParametricType("org.apache.spark.rdd.RDD",List(_)))
                    => true
                  case _ => false
                }
          } catch { case _ : Throwable => false }
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

  def seq ( e: Expr, s: Set[String] ): Boolean = {
    val r = freevars(e).toSet
    r == s || r.subsetOf(s)
  }

  /* finds a sequence of predicates in qs that imply x=y */
  def findEqPred ( xs: Set[String], ys: Set[String], qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Predicate(MethodCall(e1,"==",List(e2)))
                    => ((seq(e1,xs) && seq(e2,ys)) || (seq(e2,xs) && seq(e1,ys)))
                  case _ => false },
                { case (p::s)
                    => findEqPred(xs,ys,s) match {
                          case None => Some(List(p))
                          case Some(r) => Some(p::r)
                       }
                  case _ => None })

  /* matches ...,p1 <- e1,...,p2 <- e2,...,e3 == e4,...   */
  def findJoin ( qs: List[Qualifier] ): Option[List[Qualifier]]
    = matchQ(qs,{ case Generator(_,e1) if isRDD(e1) => true; case _ => false },
                { case (g1@Generator(p1,e1))::r1
                    => matchQ(r1,{ case Generator(_,e2) if isRDD(e2) => true; case _ => false },
                                 { case (g2@Generator(p2,e2))::r2
                                     => for { c <- findEqPred(patvars(p1).toSet,patvars(p2).toSet,r2)
                                            } yield g1::g2::c
                                  case _ => None })
                  case _ => None })

  @scala.annotation.tailrec
  def rdd_reducebykey ( hs: List[Expr], qs: List[Qualifier] ): (List[Expr],List[Qualifier])
    = qs.span{ case GroupByQual(_,_) => false; case _ => true } match {
              case (r,GroupByQual(p,k)::s)
                => val groupByVars = patvars(p)
                   val usedVars = freevars(Comprehension(hs,s),groupByVars)
                                              .intersect(comprVars(r)).distinct
                   val rt = findReducedTerms(yieldReductions(Comprehension(hs,s),usedVars),
                                             usedVars)
                   val gs = rt.map(_._2)
                              .map{ case reduce(_,Var(v))
                                      => Var(v)
                                    case reduce(_,flatMap(Lambda(p,Sequence(List(u))),Var(v)))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"flatMap",List(Lambda(p,Sequence(List(u))))))
                                      => Apply(Lambda(p,u),Var(v))
                                    case reduce(_,MethodCall(Var(v),"map",List(g)))
                                      => Apply(g,Var(v))
                                    case e
                                      => Sequence(List(e))
                                  }
                   val ms = rt.map{ case (_,reduce(m,_)) => m
                                    case (_,_) => "++"
                                  }
                   val m = if (ms.length == 1)
                              Lambda(TuplePat(List(VarPat("x"),VarPat("y"))),
                                     MethodCall(Var("x"),ms.head,List(Var("y"))))
                           else { val xs = rt.map(_ => newvar)
                                  val ys = rt.map(_ => newvar)
                                  Lambda(TuplePat(List(TuplePat(xs.map(VarPat)),
                                                       TuplePat(ys.map(VarPat)))),
                                         Tuple((ms zip (xs zip ys))
                                                 .map{ case (m,(x,y))
                                                         => MethodCall(Var(x),m,List(Var(y))) }))
                                }
                   val env = rt.map{ case (n,e) => (e,newvar) }
                   def lift ( x: Expr ): Expr
                     = env.foldLeft(x) { case (r,(from,to)) => AST.subst(from,Var(to),r) }
                   val Comprehension(nhs,ns) = lift(Comprehension(hs,s))
                   val red = MethodCall(Call("rdd",List(Comprehension(List(Tuple(List(toExpr(p),Tuple(gs)))),r))),
                                        "reduceByKey",List(m))
                   rdd_reducebykey(nhs,Generator(TuplePat(List(p,TuplePat(env.map(x => VarPat(x._2))))),
                                                 red)::ns)
              case _
                => findJoin(qs) match {
                     case Some((g1@Generator(p1,d1))::(g2@Generator(p2,d2))::cs)
                       => val jt1 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (seq(e1,patvars(p1).toSet)) e1 else e2
                                                  case _ => d1 })
                          val jt2 = tuple(cs.map{ case Predicate(MethodCall(e1,"==",List(e2)))
                                                    => if (seq(e1,patvars(p2).toSet)) e1 else e2
                                                  case _ => d1 })
                          val left = flatMap(Lambda(p1,Sequence(List(Tuple(List(jt1,toExpr(p1)))))),d1)
                          val right = flatMap(Lambda(p2,Sequence(List(Tuple(List(jt2,toExpr(p2)))))),d2)
                          val z = Generator(TuplePat(List(p1,p2)),
                                            flatMap(Lambda(TuplePat(List(VarPat("_k"),VarPat("x"))),
                                                           Sequence(List(Var("x")))),
                                                    MethodCall(left,"join",List(right))))
                          rdd_reducebykey(hs,qs.flatMap(x => if (x == g1) List(z)
                                                             else if (x == g2 || cs.contains(x)) Nil
                                                             else List(x)))
                     case _ 
                       =>  (hs,qs)
                   }
    }

  def translate ( e: Expr ): Expr = {
    e match {
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
      case Call("array",List(Lambda(VarPat(nv),c@Comprehension(List(_),_)),u))
        if optimize
        => subst(nv,lift_array_expr(Var(nv),typecheck_expr(u)),c) match {
              case Comprehension(hs,qs)
                => val (List(h),nqs) = translate_comprehension(hs,qs)
                   val k = newvar
                   val v = newvar
                   val nr = nqs :+ LetBinding(TuplePat(List(VarPat(k),VarPat(v))),h) :+
                                   AssignQual(MapAccess(Var(nv),Var(k)),Var(v))
                   translate(Block(List(VarDecl(nv,MethodCall(u,"clone",null)),
                                        Comprehension(Nil,nr),Var(nv))))
              case _ => e
           }
      case Call("array",List(Lambda(VarPat(nv),c@Comprehension(_,_)),u))
        if optimize
        => subst(nv,lift_array_expr(Var(nv),typecheck_expr(u)),c) match {
              case Comprehension(hs,qs)
                => val (nhs,nqs) = translate_comprehension(hs,qs)
                   val vs = nhs.map( x => (newvar,newvar) )
                   val ls = (nhs zip vs).map{ case (h,(k,v)) => LetBinding(TuplePat(List(VarPat(k),VarPat(v))),h) }
                   val nr = nqs ++ ls :+ AssignQual(Tuple(vs.map{ case (k,_) => MapAccess(Var(nv),Var(k)) }),
                                                    Tuple(vs.map{ case (_,v) => Var(v) }))
                   translate(Block(List(VarDecl(nv,MethodCall(u,"clone",null)),
                                        Comprehension(Nil,nr),Var(nv))))
              case _ => e
           }
      case reduce(op,Comprehension(hs,qs))
        if optimize
        => val (nhs,nqs) = translate_comprehension(hs,qs)
           val nv = newvar
           val nr = nqs ++ nhs.map { case h => AssignQual(Var(nv),MethodCall(Var(nv),op,List(h))) }
           val zero = op match { case "+" => IntConst(0); case "*" => IntConst(1)
                                 case "&&" => BoolConst(true); case "||" => BoolConst(false) }
           translate(Block(List(VarDecl(nv,zero),
                                Comprehension(Nil,nr),Var(nv))))
      case Call(array,List(Tuple(d),Comprehension(hs,qs)))
        if optimize
        => val (nhs,nqs) = translate_comprehension(hs,qs)
           val nv = newvar
           val nr = nqs ++ nhs.flatMap {
                              case h => val (kv,v) = (newvar,newvar)
                                        List(LetBinding(TuplePat(List(VarPat(kv),VarPat(v))),h),
                                             AssignQual(MapAccess(Var(nv),Var(kv)),Var(v))) }
           translate(Block(List(VarDecl(nv,Call(array,d)),
                                Comprehension(Nil,nr),Var(nv))))
      case Call(array,List(Tuple(d),Comprehension(hs,qs)))
        if optimize
        => val (nhs,nqs) = translate_comprehension(hs,qs)
           val nv = newvar
           val nr = nqs ++ nhs.flatMap {
                              case h => val (kv,v) = (newvar,newvar)
                                        List(LetBinding(TuplePat(List(VarPat(kv),VarPat(v))),h),
                                             AssignQual(MapAccess(Var(nv),Var(kv)),Var(v))) }
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
      case Call("rdd",List(Comprehension(hs,qs)))
        if optimize
        => val (nhs,nqs) = rdd_reducebykey(hs,qs)
           return apply(Comprehension(nhs,nqs),translate)
      case Comprehension(result,qs)
        if optimize
        => val (nhs,nqs) = translate_comprehension(result,qs)
           apply(Comprehension(nhs,nqs),translate)
      case _ => apply(e,translate)
    }
  }
}
