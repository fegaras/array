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

case class Matrix ( rows: Int, cols: Int ) {
  var V = Array.fill(rows*cols)(0.0D)

  def head = V(0)

  def apply ( i: Int, j: Int ): Double = {
    assert( i>=0 && i<rows && j>=0 && j<cols )
    V(i*rows+j)
  }

  def update ( i: Int, j: Int, v: Double ) {
    assert( i>=0 && i<rows && j>=0 && j<cols )
    V(i*rows+j) = v
  }
}

object Matrix {
  def tabulate ( rows: Int, cols: Int ) ( f: (Int,Int) => Double ): Matrix = {
    val m = Matrix(rows,cols)
    (0 until rows).foreach{ i => (0 until cols).foreach{ j => m(i,j) = f(i,j) } }
    m
  }
}
