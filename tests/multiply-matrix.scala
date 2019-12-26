import scala.util._
import edu.uta.array._

object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val M = Matrix.tabulate(n,n){ (i,j) => rand.nextDouble() }
    val N = Matrix.tabulate(n,n){ (i,j) => rand.nextDouble() }

    var t: Long = System.currentTimeMillis()

    ar("""
       Matrix(n,n)[ (+/v)[i,j] | m[i,k] <- M, n[kk,j] <- N, v = m*n, k == kk, group by (i,j) ]
    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
