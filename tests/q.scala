import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt
    val m = n
val N = n
val M = N

    val X = Array.tabulate(n){ i => rand.nextDouble() }
    val Y = Array.tabulate(n){ i => rand.nextDouble() }

    ar("""

array(N*M)[ (k,+/v) | (i,x) <- X, (j,y) <- Y, i%M == j/M, v = x*y, group by k: i/M*M+j/M ]


       """)

  }
}
