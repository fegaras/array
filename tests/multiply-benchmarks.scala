import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    param(optimize,true)

    for ( k <- 1 to 10 ) {
      val n = (1000*Math.sqrt(k/10.0)).toInt
      val M = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
      val N = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
      var s = 0L
      for ( i <- 1 to 10 ) {
        val t = System.currentTimeMillis()
        ar("""
            array(n,n)[ (+/v)[i,j] | m[i,k] <- M, n[kk,j] <- N, v = m*n, k == kk, group by (i,j) ]
        """)
        s += System.currentTimeMillis()-t
      }
      println("**** Array size: "+n*n+" run time: "+(s/10.0)/1000.0+" secs")
      s = 0L
      for ( i <- 1 to 10 ) {
        val t = System.currentTimeMillis()
        Array.tabulate(n,n){ case (i,j) => (0 until n).map{ k => M(i)(k)*N(k)(j) }.reduce(_+_) }
        s += System.currentTimeMillis()-t
      }
      println("**** Tabulate size: "+n*n+" run time: "+(s/10.0)/1000.0+" secs")
    }
  }
}
