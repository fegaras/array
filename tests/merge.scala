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
//WRONG
       //Array(20)[ (i+j,v) | v[i] <- V, w[j] <- W, z[k] <- W, k==j+1, w<=v, v<z ]
       Array((V.length)+W.length)[ v[i+j], w[i+j+1]
                      | v[i] <- V, vv[ii] <- V, ii==i+1, ii<5, w[j] <- W, v<=w, w<=vv ]

       """)
x.foreach(println)

  }
}
