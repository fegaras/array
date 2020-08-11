import edu.uta.array._
import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.util.Random
import Math._


object Factorization extends Serializable {
  /* The size of any serializable object */
  def sizeof ( x: Serializable ): Int = {
    import java.io.{ByteArrayOutputStream,ObjectOutputStream}
    val bs = new ByteArrayOutputStream()
    val os = new ObjectOutputStream(bs)
    os.writeObject(x)
    os.flush()
    os.close()
    bs.toByteArray().length
  }

  val a = 0.002
  val b = 0.02

  implicit class Mult ( private val value: Double ) extends AnyVal {
    def ^ ( that: Double ): Double
      = value+(1-a*b)*that
  }

  def main ( args: Array[String] ) {
    val repeats = args(0).toInt
    val n = args(1).toInt
    val m = args(2).toInt
    val d = args(3).toInt  // number of attributes
    val mode = args(4) == "1"
    parami(tileSize,1000) // each tile has size N*N
    val N = tileSize

    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

    def randomTile (): DenseMatrix = {
      val max = 5
      val rand = new Random()
      new DenseMatrix(N,N,Array.tabulate(N*N){ i => rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
      val l = Random.shuffle((0 until (rows+N-1)/N).toList)
      val r = Random.shuffle((0 until (cols+N-1)/N).toList)
      sc.parallelize(for { i <- l; j <- r } yield (i,j))
        .map{ case (i,j) => ((i,j),randomTile()) }
    }

    val Rm = randomMatrix(n,m)
    val Pm = randomMatrix(n,d)
    val Qm = randomMatrix(m,d)

    val R = new BlockMatrix(Rm,N,N)
    val Pinit = new BlockMatrix(Pm,N,N)
    val Qinit = new BlockMatrix(Qm,N,N)

    val RR = (n,m,Rm.map{ case ((i,j),a) => ((i,j),a.toArray) })
    val PPinit = (n,d,Pm.map{ case ((i,j),a) => ((i,j),a.toArray) })
    val QQinit = (m,d,Qm.map{ case ((i,j),a) => ((i,j),a.toArray) })

    def map ( m: BlockMatrix, f: Double => Double ): BlockMatrix
      = new BlockMatrix(m.blocks.map{ case (i,a) => (i,new DenseMatrix(N,N,a.toArray.map(f))) },
                        m.rowsPerBlock,m.colsPerBlock)

    def testFactorizationMLlib(): Double = {
      val t = System.currentTimeMillis()
      var E = R
      var P = Pinit
      var Q = Qinit
      try {
        E = R.subtract(P.multiply(Q.transpose))
        P = P.add(map(map(E.multiply(Q),2*_).subtract(map(P,b*_)),a*_))
        Q = Q.add(map(map(E.transpose.multiply(P),2*_).subtract(map(Q,b*_)),a*_))
      val x = E.blocks.count+P.blocks.count+Q.blocks.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testFactorizationDiablo(): Double = {
      val t = System.currentTimeMillis()
      var E = RR
      var P = PPinit
      var Q = QQinit
      try {
        val E2 = ar("""
                    tiled(n,m)[ (+/v)[i,j] | p[i,k] <- P, q[kk,j] <- Q,
                                             kk == k, v = p*q, group by (i,j) ]
                    """)
        E = ar("""
               tiled(n,m)[ (r - v)[i,j] | r[i,j] <- RR, v[ii,jj] <- E2, ii == i, jj == j, r > 0.0 ]
               """)
        P = ar("""
               tiled(n,d)[ (^/v)[i,k]
                         | e[i,j] <- E, q[k,jj] <- Q, jj == j,
                           v = 2*0.002*e*q, group by (i,k) ]
             """)
        Q = ar("""
               tiled(m,d)[ (^/v)[k,j]
                         | e[i,j] <- E, p[ii,k] <- P, ii == i,
                           v = 2*0.002*e*p, group by (k,j) ]
               """)
        val x = E._3.count+P._3.count+Q._3.count
      } catch { case x: Throwable => println(x); return -1.0 }
      (System.currentTimeMillis()-t)/1000.0
    }

    def test ( name: String, f: => Double ) {
      val cores = Runtime.getRuntime().availableProcessors()
      var i = 0
      var j = 0
      var s = 0.0
      while ( i < repeats && j < 10 ) {
        val t = f
        j += 1
        if (t > 0.0) {   // if f didn't crash
          i += 1
          println("Try: "+i+"/"+j+" time: "+t)
          s += t
        }
      }
      if (i > 0) s = s/i
      print("*** %s cores=%d n=%d m=%d d=%d N=%d %.2f GB ".format(name,cores,n,m,d,N,(8.0*n.toDouble*n)/(1024.0*1024.0*1024.0)))
      println("tries=%d %.3f secs".format(i,s))
    }

    if (!mode)
      test("MLlib Factorization",testFactorizationMLlib)
    else test("DIABLO Factorization",testFactorizationDiablo)

    sc.stop()
  }
}
