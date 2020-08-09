import scala.util._
import edu.uta.array._
import scala.util._


object Test {
  val a = 0.0002
  val b = 0.02

  implicit class Mult ( private val value: Double ) extends AnyVal {
    def ^ ( that: Double ): Double
      = value+(1-a*b)*that
  }

  def main ( args: Array[String] ) {
    val n = args(0).toInt
    val m = args(1).toInt
    val d = args(2).toInt
    val iterations = 1
    val rand = new Random()

    val R = Array.tabulate(n,m){ case (i,j) => if (rand.nextDouble > 0.1) 0 else Math.floor(rand.nextDouble()*5+1).toInt }
    val Pinit = Array.tabulate(n,d){ case (i,j) => rand.nextDouble()*2 }
    val Qinit = Array.tabulate(d,m){ case (i,j) => rand.nextDouble()*2 }
    var P = Pinit
    var Q = Qinit

    var t: Long = System.currentTimeMillis()

    for ( _ <- 1 to iterations ) {
      val E = ar("""
                 array(n,m)[ (r - +/v)[i,j] | p[i,k] <- P, q[kk,j] <- Q,
                                              kk == k, v = p*q, group by (i,j),
                                              r[ii,jj] <- R, ii == i, jj == j, r > 0.0 ]
                 """)
      P = ar("""
             array(n,d)[ (^/v)[i,k]
                       | e[i,j] <- E, q[k,jj] <- Q, jj == j,
                         v = 2*a*e*q, group by (i,k) ]
             """)
      Q = ar("""
             array(d,m)[ (^/v)[k,j]
                       | e[i,j] <- E, p[ii,k] <- P, ii == i,
                         v = 2*a*e*p, group by (k,j) ]
             """)
      //for ( i <- 0 until n; j <- 0 until m if E(i)(j)>0.0) println("@@@ "+i+" "+j+" "+E(i)(j))
    }

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    //for(i <- 0 to 5) println(P(i)(0))
    //for(i <- 0 to 5) println(Q(0)(i))

    P = Pinit
    Q = Qinit

    t = System.currentTimeMillis()

    for ( _ <- 1 to iterations;
          i <- 0 until n;
          j <- 0 until m if R(i)(j) > 0
        ) {
          var e = 0.0
          for ( k <- 0 until d )
              e += P(i)(k)*Q(k)(j)
          e = R(i)(j) - e
//if (i < n && j < m && e > 0.0) println("@@@ "+i+" "+j+" "+e)
          for ( k <- 0 until d ) {
              P(i)(k) += a*(2*e*Q(k)(j)-b*P(i)(k))
              Q(k)(j) += a*(2*e*P(i)(k)-b*Q(k)(j))
          }
    }

    println("**** run time: "+(System.currentTimeMillis()-t)/1000.0+" secs")

    //for(i <- 0 to 5) println(P(i)(0))
    //for(i <- 0 to 5) println(Q(0)(i))

  }
}
