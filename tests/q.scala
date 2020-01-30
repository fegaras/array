import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt
    val m = n

    val M = Array.tabulate(n,m){ (i,j) => rand.nextDouble() }

    //val X = Array.tabulate(n,m,n){ (i,j,k) => rand.nextDouble() }

    ar("""

       Array(M)[ x[i,j], (x+1)[j,i] | x[i,j] <- M ]
/*
       Array(n)[ (+/v / v.length)[i]
               | v[i,j] <- M,
                 group by i ].foreach(println)
*/
       """)

  }
}
