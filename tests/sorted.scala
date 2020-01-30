import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    //val n = args(0).toInt

    //val V = Array.tabulate(n){ i => rand.nextDouble() }

    val V = args

    val x = ar("""

       &&/[ v<=w | v[i] <- V, w[j] <- V, j<V.length, j==i+1 ]

       """)
println(x)

  }
}
