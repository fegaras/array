import org.apache.spark._
import org.apache.spark.rdd._
import org.apache.spark.mllib.linalg.distributed._
import org.apache.spark.mllib.linalg._
import org.apache.log4j._
import org.apache.hadoop.fs._
import scala.util.Random
import Math._

object Tiles {
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

  def main ( args: Array[String] ) {
    val repeats = args(0).toInt
    val n = args(1).toInt   // each matrix has n*n elements
    val N = 1000

    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

    type TiledMatrix = RDD[((Int,Int),Array[Double])]
    type MLlibMatrix = RDD[((Int, Int),Matrix)]

    def randomTile (): DenseMatrix = {
      val max = 10
      val rand = new Random()
      new DenseMatrix(N,N,Array.tabulate(N*N){ i => rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): MLlibMatrix = {
      val l = Random.shuffle((0 until rows/N).toList)
      val r = Random.shuffle((0 until cols/N).toList)
      sc.parallelize(for { i <- l; j <- r } yield (i,j))
        .map{ case (i,j) => ((i,j),randomTile()) }
    }

    val Am = randomMatrix(n,n)
    val Bm = randomMatrix(n,n)

    val A = new BlockMatrix(Am,N,N)
    val B = new BlockMatrix(Bm,N,N)
    A.validate()
    B.validate()

    val AA: TiledMatrix = Am.map{ case ((i,j),a) => ((i,j),a.toArray) }
    val BB: TiledMatrix = Bm.map{ case ((i,j),a) => ((i,j),a.toArray) }

    def multiplyMLlib (): BlockMatrix = {
      val C = A.multiply(B)
      val x = C.blocks.count
      C
    }

    def multiplyDiablo (): TiledMatrix = {
      val C = AA.flatMap{ case ((i,k),a) => (0 until n/N).map(j => ((i,j),(k,a))) }
                .cogroup( BB.flatMap{ case ((k,j),b) => (0 until n/N).map(i => ((i,j),(k,b))) } )
                .mapValues{ case (as,bs)
                              => val c = Array.fill(N*N)(0.0)
                                 for { (k1,a) <- as
                                       (k2,b) <- bs if k2 == k1
                                       i <- (0 until N).par
                                       k <- 0 until N
                                       j <- 0 until N
                                     } c(i*N+j) += a(i*N+k)*b(k*N+j)
                                 c
                          }
      val x = C.count
      C  
    }

    def mult ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N).par }
           for { j <- 0 until N }
               for { k <- 0 until N }
                   V(i*N+j) += x(i*N+k)*y(k*N+j)
       V
    }

    def add ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N).par
             j <- 0 until N }
           V(i*N+j) = x(i*N+j)+y(i*N+j)
       V
    }

    def multiplyDiabloGB (): TiledMatrix = {
      val S = AA.map{ case ((i,k),a) => (k,(i,a)) }
                .join( BB.map{ case ((kk,j),b) => (kk,(j,b)) } )
                .map{ case (_,((i,a),(j,b))) => ((i,j),mult(a,b)) }
                .reduceByKey(add)
      val c = S.count
      S
    }

    def test ( name: String, f: () => Any ) {
      val cores = Runtime.getRuntime().availableProcessors()
      val t: Long = System.currentTimeMillis()
      for ( i <- 1 to repeats ) f()
      val s = (System.currentTimeMillis()-t)/1000.0
      print("*** %s cores=%d n=%d N=%d %.2f GB ".format(name,cores,n,N,(8.0*n.toDouble*n)/(1024.0*1024.0*1024.0)))
      println("%.3f secs".format(s/repeats))
    }

    test("DIABLO Multiply",multiplyDiablo)
    test("DIABLO/GB Multiply",multiplyDiabloGB)
    test("MLlib Multiply",multiplyMLlib)

    sc.stop()
  }
}
