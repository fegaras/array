import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val V = Array.tabulate(n){ i => Math.abs(rand.nextInt()) % 1000 }

    val x = ar("""

       Array(V)[ v[j], w[i] | v[i] <- V, w[j] <- V, i<j, v>w ]

       """)

    x.foreach(println)

  }
}
