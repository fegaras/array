import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val M = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
    val N = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }

    param(optimize,true)

    var t: Long = System.currentTimeMillis()

    ar("""
       array(n,n)[ (+/v)[i,j] | m[i,k] <- M, n[kk,j] <- N, v = m*n, k == kk, group by (i,j) ]
    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    t = System.currentTimeMillis()

    Array.tabulate(n,n){ case (i,j) => (0 until n).map{ k => M(i)(k)*N(k)(j) }.reduce(_+_) }

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    t = System.currentTimeMillis()

    Array.tabulate(n,n){ case (i,j) => (0 until n).foldLeft[Double](0.0){ (r,k) => r+M(i)(k)*N(k)(j) } }

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")
  }
}
