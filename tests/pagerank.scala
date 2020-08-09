import scala.util._
import edu.uta.array._
import scala.util._
import scala.annotation.tailrec


object Test {
  def main ( args: Array[String] ) {
    val vertices = args(0).toInt
    val edges = args(1).toInt

    var rand = new Random()
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

    val G = Array.ofDim[List[Int]](vertices)
    for ( i <- 0 until vertices )
      G(i) = Nil

    for ( k <- 1 to edges ) {
      val (i,j) = addEdge(vertices)
      G(i) = j::G(i)
    }

    var ranks = Array.fill[Double](vertices)(1.0/vertices)

    var t: Long = System.currentTimeMillis()

    for ( k <- 1 to 10 )
      ranks = ar("""
                 array(vertices)[ (link,+/in)
                                | rank[i] <- ranks, links[j] <- G, i == j,
                                  in = rank/(links.length),
                                  link <- links, group by link ]
                 """)

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    for(i<-0 to 9) println(ranks(i))

    ranks = Array.fill[Double](vertices)(1.0/vertices)

    t = System.currentTimeMillis()

    for ( k <- 1 to 10 ) {
       val nranks = Array.fill[Double](vertices)(0.0)
       for ( i <- 0 until vertices ) {
          val len = G(i).length
          for ( link <- G(i) )
             nranks(link) += ranks(i)/len
       }
       ranks = nranks
    }

/*
    for ( k <- 1 to 10;
          i <- 0 until vertices;
          len = G(i).length;
          link <- G(i) )
        ranks(link) += ranks(i)/len
*/

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    for(i<-0 to 9) println(ranks(i))
  }
}
