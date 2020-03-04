import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val A = Array.tabulate(n){ i => Math.abs(rand.nextInt()) % 1000 }

    val x = ar("""

       //array(V)[ v[j], w[i] | v[i] <- V, w[j] <- V, i<j, v>w ]
       array{ V => [ v[j], w[i] | v[i] <- V, w[j] <- V, i<j, v>w ] } A

       """)

    x.foreach(println)

  }
}
