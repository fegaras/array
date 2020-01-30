import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    //val n = args(0).toInt

    //val V = Array.tabulate(n){ i => rand.nextDouble() }
    val V = Array(1,3,4,4,6)
    val W = Array(1,2,7,9)

    val x = ar("""

      V ++ Array(W.length)[ w[(W.length)-i-1] | w[i] <- W ]

       """)
x.foreach(println)

  }
}
