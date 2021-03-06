import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    val n = args(0).toInt

    val M = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }

    var t: Long = System.currentTimeMillis()

    ar("""
       [ ((+/m)[i],*/m,+/j,j.length,+/(m.map(x => x+3.0))) | m[i,j] <- M, group by i ]

    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
