import scala.util._
import edu.uta.array._
import scala.util._
import scala.annotation.tailrec


object Test {
  def main ( args: Array[String] ) {
    val vertices = args(0).toInt
    val edges = args(1).toInt
    val repeats = 10
    val iterations = 10
    val experiments = 10
    val rand = new Random()

    val RMATa = 0.30
    val RMATb = 0.25
    val RMATc = 0.20
    val RMATd = 0.25

    def pickQuadrant ( a: Double, b: Double, c: Double, d: Double ): Int
      = rand.nextDouble() match {
          case x if x < a => 0
          case x if (x >= a && x < a + b) => 1
          case x if (x >= a + b && x < a + b + c) => 2
          case _ => 3
        }

    @tailrec
    def chooseCell ( x: Int, y: Int, t: Int ): (Int,Int) = {
        if (t <= 1)
           (x,y)
        else {
           val newT = math.ceil(t.toFloat/2.0).toInt
           pickQuadrant(RMATa, RMATb, RMATc, RMATd) match {
             case 0 => chooseCell(x, y, newT)
             case 1 => chooseCell(x + newT, y, newT)
             case 2 => chooseCell(x, y + newT, newT)
             case 3 => chooseCell(x + newT, y + newT, newT)
           }
        }
    }

    @tailrec
    def addEdge ( vn: Int ): (Int,Int) = {
       val p@(x,y) = chooseCell(0,0,vn)
       if (x >= vn || y >= vn)
         addEdge(vn)
       else p
    }

    param(optimize,true)

    for ( q <- 1 to experiments ) {
      val vn = vertices/experiments*q
      val en = edges/experiments*q

      val G = Array.ofDim[List[Int]](vn)
      for ( i <- 0 until vn )
         G(i) = Nil

      for ( k <- 1 to en ) {
         val (i,j) = addEdge(vn)
         G(i) = j::G(i)
      }
 
      var t: Long = System.currentTimeMillis()

      for ( _ <- 1 to repeats ) {
         var ranks = Array.fill[Double](vn)(1.0/vn)
         for ( k <- 1 to iterations )
            ranks = ar("""
                       array(vn)[ (link,+/in)
                                | rank[i] <- ranks, links[j] <- G, i == j,
                                  in = rank/(links.length),
                                  link <- links, group by link ]
                       """)
      }

      println("**** Array vertices: %d, edges: %d, run time: %.2f secs"
              .format(vn,en,(System.currentTimeMillis()-t)/1000.0/repeats))

      t = System.currentTimeMillis()

      for ( _ <- 1 to repeats ) {
         var ranks = Array.fill[Double](vn)(1.0/vn)
         for ( k <- 1 to iterations ) {
            val nranks = Array.fill[Double](vn)(0.0)
            for ( i <- 0 until vn ) {
               val len = G(i).length
               for ( link <- G(i) )
                  nranks(link) += ranks(i)/len
            }
            ranks = nranks
         }
      }

      println("**** Scala vertices: %d, edges: %d, run time: %.2f secs"
              .format(vn,en,(System.currentTimeMillis()-t)/1000.0/repeats))
    }
  }
}
