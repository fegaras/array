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
package edu.uta

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros
import scala.reflect.ClassTag
import array.Parser.parse
import array.Translator.translate

import scala.collection.mutable

package object array {

  var optimize = true
  var trace = true

  def array[T: ClassTag] ( length: Int ) ( values: List[(Int,T)] ): Array[T] = {
    val a = Array.ofDim[T](length)
    for { (i,v) <- values }
        if (i>=0 && i<length)
           a(i) = v
    a
  }

  def array[T: ClassTag] ( rows: Int, cols: Int ) ( values: List[((Int,Int),T)] ): Array[Array[T]] = {
    val a = Array.ofDim[T](rows,cols)
    for { ((i,j),v) <- values }
        if (i>=0 && i<rows && j>=0 && j<cols)
           a(i)(j) = v
    a
  }

  def map[K,V] ( s: List[(K,V)] ): mutable.Map[K,V] = {
    val m = mutable.HashMap[K,V]()
    for { (k,v) <- s }
        m += (k -> v)
    m
  }

  def array[T] ( a: Array[T] ) ( values: List[(Int,T)] ): Array[T] = {
    for { (i,v) <- values }
        if (i>=0 && i<a.length)
           a(i) = v
    a
  }

  def array[T] ( a: Array[Array[T]] ) ( values: List[((Int,Int),T)] ): Array[Array[T]] = {
    for { ((i,j),v) <- values }
        if (i>=0 && i<a.length && j>=0 && j<a(i).length)
           a(i)(j) = v
    a
  }

  def map[K,V] ( m: mutable.Map[K,V] ) ( s: List[(K,V)] ): mutable.Map[K,V] = {
    for { (k,v) <- s }
        m += (k -> v)
    m
  }

  def translate_query ( query: String ): Expr = {
    val q = parse(query)
    if (trace) println("Term:\n"+Pretty.print(q.toString))
    val c = ComprehensionTranslator.translate(q)
    if (trace) println("Translated comprehension:\n"+Pretty.print(c.toString))
    val n = Normalizer.normalizeAll(c)
    if (trace) println("Normalized comprehension:\n"+Pretty.print(n.toString))
    val o = Normalizer.normalizeAll(Optimizer.optimizeAll(n))
    if (trace) println("Optimized comprehension:\n"+Pretty.print(o.toString))
    val e = Normalizer.normalizeAll(translate(o))
    if (trace) println("Translated term:\n"+Pretty.print(e.toString))
    e
  }

  var typecheck_var: String => Option[Type] = _
  var typecheck_expr: Expr => Option[Type] = _

  def ar_impl ( c: Context ) ( query: c.Expr[String] ): c.Expr[Any] = {
    import c.universe.{Expr=>_,Type=>_,_}
    val context: c.type = c
    val cg = new { val c: context.type = context } with CodeGeneration
    val Literal(Constant(s:String)) = query.tree
    // hooks to the Scala compiler
    typecheck_var = ( v: String ) => cg.typecheckOpt(Var(v)).map(cg.Tree2Type)
    typecheck_expr = ( e: Expr) => cg.typecheckOpt(e).map(cg.Tree2Type)
    val e = translate_query(s)
    val env: cg.Environment = Map()
    val ec = cg.codeGen(e,env)
    if (trace) println("Scala code:\n"+showCode(ec))
    val tp = cg.getType(ec,env)
    if (trace) println("Scala type: "+showCode(tp))
    context.Expr[Any](ec)
  }

  /** translate an array comprehension to Scala code */
  def ar ( query: String ): Any = macro ar_impl

  def param_impl ( c: Context ) ( x: c.Expr[Boolean], b: c.Expr[Boolean] ): c.Expr[Unit] = {
    import c.universe._
    val Literal(Constant(bv:Boolean)) = b.tree
    x.tree.toString.split('.').last match {
       case "optimize" => optimize = bv
       case "trace" => trace = bv
       case p => throw new Error("Wrong param: "+p)
    }
    c.Expr[Unit](q"()")
   }

  /** set compilation parameters */
  def param ( x:Boolean, b: Boolean ): Unit = macro param_impl
}

object Test {
  import array.Pretty

  def main ( args: Array[String] ) {
    val e = parse(args(0))
    println(Pretty.print(e.toString))
    val te = translate(e)
    println(print(te.toString))
  }
}
