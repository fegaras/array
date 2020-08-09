import scala.util._
import edu.uta.array._


object Test {
  val rand = new Random()

  def main ( args: Array[String] ) {

    val M = new Tile(Array.tabulate(Tile.size*Tile.size){ i => rand.nextDouble() })
    val N = new Tile(Array.tabulate(Tile.size*Tile.size){ i => rand.nextDouble() })

    var t: Long = System.currentTimeMillis()

    ar("""
       //tile()[ (m+n)[i,j] | m[i,j] <- M, n[ii,jj] <- N, ii == i, jj == j ]
       tile()[ (+/v)[i,j] | m[i,k] <- M, n[kk,j] <- N, kk == k, v = m*n, group by (i,j) ]
    """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

  }
}
