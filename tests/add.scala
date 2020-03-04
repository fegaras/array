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
       array(n,n)[ (m+n)[i,j] | m[i,j] <- M, n[ii,jj] <- N, ii == i, jj == j ]
    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    t = System.currentTimeMillis()

    Array.tabulate(n,n){ case (i,j) => M(i)(j)+N(i)(j) }
    //(M zip N).map{ case (ns,ms) => (ns zip ms).map{ case (n,m) => n+m }.toArray }.toArray

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")
  }
}
