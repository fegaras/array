import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    //val n = args(0).toInt

    //val A = Array.tabulate(n){ i => rand.nextDouble() }
    val A = Array(5,3,4,1,6,8)

    def random ( n: Int ) = Math.abs(rand.nextInt())% n

    val x = ar("""

       array{ V => [ v[j], w[i] | v[i] <- V, w[j] <- V, j==random(V.length) ] } A

       """)

    x.foreach(println)

  }
}
