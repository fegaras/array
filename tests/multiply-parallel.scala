import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {
    println("Number of cores: "+Runtime.getRuntime().availableProcessors())
    println("Memory: "+(Runtime.getRuntime.maxMemory / 1024))

    for ( k <- 1 to 10 ) {
      val n = (2000*Math.sqrt(k/10.0)).toInt
      val M = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
      val N = Array.tabulate(n,n){ (i,j) => rand.nextDouble() }
      var s = 0L
      for ( i <- 1 to 10 ) {
        val v1 = Array.ofDim[Double](n, n);
        val t = System.currentTimeMillis()
        0.until(M.length).par.foreach(((v8: Int) => 0.until(Math.min(M(v8).length, N.length)).foreach(((v9: Int) => 0.until(N(v9).length).foreach(((v11: Int) => v1(v8).update(v11, v1(v8)(v11).+(M(v8)(v9).*(N(v9)(v11))))))))));
        s += System.currentTimeMillis()-t
      }
      println("**** Parallel size: "+n*n+" run time: "+(s/10.0)/1000.0+" secs")
    }
  }
}
