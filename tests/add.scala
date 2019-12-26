import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val M = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
    val N = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }

    var t: Long = System.currentTimeMillis()

    ar("""
       Array(n,n)[ (m+n)[i,j] | m[i,j] <- M, n[ii,jj] <- N, ii == i, jj == j ]
    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
