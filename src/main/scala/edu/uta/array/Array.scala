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

import array.Parser.parse
import array.Translator.translate

package object array {

  var optimize = true
  var trace = true

  def translate_query ( query: String ): Expr = {
    val q = parse(query)
    if (!optimize)
      return translate(q)
    if (trace) println("Term:\n"+Pretty.print(q.toString))
    val c = ComprehensionTranslator.translate(q)
    if (trace) println("Translated comprehension:\n"+Pretty.print(c.toString))
    val n = Normalizer.normalizeAll(c)
    if (trace) println("Normalized comprehension:\n"+Pretty.print(n.toString))
    val o = Normalizer.normalizeAll(Optimizer.optimizeAll(n))
    if (trace) println("Optimized comprehension:\n"+Pretty.print(o.toString))
    val e = translate(o)
    if (trace) println("Translated term:\n"+Pretty.print(e.toString))
    e
  }

  var typecheck_var: String => Option[Type] = _

  def ar_impl ( c: Context ) ( query: c.Expr[String] ): c.Expr[Any] = {
    import c.universe.{Expr=>_,Type=>_,_}
    val context: c.type = c
    val cg = new { val c: context.type = context } with CodeGeneration
    val Literal(Constant(s:String)) = query.tree
    // hook to the Scala compiler
    typecheck_var = ( v: String ) => cg.typecheckOpt(Var(v)).map(cg.Tree2Type)
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
