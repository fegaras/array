import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt
    val m = n

    val M = Array.tabulate(n,m){ (i,j) => rand.nextDouble() }

    var t: Long = System.currentTimeMillis()

    ar("""

       Array(n,m)[ (+/v / v.length)[I,J]
                 | v[i,j] <- M,
                   I <- (i-1) to (i+1),
                   J <- (j-1) to (j+1),
                   I >= 0, I < n, J >= 0, J < n,
                   group by (I,J) ]

       """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
