import edu.uta.array._
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
    val m = n
    val N = 1000   // each tile has size N*N

    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.ERROR)

    def randomTile (): DenseMatrix = {
      val max = 10
      val rand = new Random()
      new DenseMatrix(N,N,Array.tabulate(N*N){ i => rand.nextDouble()*max })
    }

    def randomMatrix ( rows: Int, cols: Int ): RDD[((Int, Int),org.apache.spark.mllib.linalg.Matrix)] = {
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

    val AA = (n,m,Am.map{ case ((i,j),a) => ((i,j),a.toArray) })
    val BB = (n,m,Bm.map{ case ((i,j),a) => ((i,j),a.toArray) })

    val rand = new Random()
    val AR = sc.parallelize(for { i <- 0 until n; j <- 0 until m }
                            yield ((i,j),rand.nextDouble()*10))

    def testMultiplyMLlib(): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = A.multiply(B)
        val x = C.blocks.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testMultiplyDiablo(): Double = {
      val t = System.currentTimeMillis()
      try {
        val C = ar("""
                   //tiled(n,m)[ ((i,j),+/c) | ((i,k),m) <- AA, ((kk,j),n) <- BB, k == kk, c = m*n, group by (i,j) ]
                   //tiled(n,m)[ ((i,j),+/c) | ((i,k),m) <- AA, ((kk,j),n) <- BB, k == kk, ((ii,jj),mm) <- AA, i==ii, k==jj, c = m*n*mm, group by (i,j) ]
                   //tiled(n,m)[ ((i,j),m+1) | ((i,j),m) <- AA ]
                   tiled(n,m)[ ((j,i),m) | ((i,j),m) <- AA ]
                   """)
        val x = C.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def test ( name: String, f: () => Double ) {
      val cores = Runtime.getRuntime().availableProcessors()
      val s = (for ( i <- 1 to repeats ) yield f()).sum
      print("*** %s cores=%d n=%d N=%d %.2f GB ".format(name,cores,n,N,(8.0*n.toDouble*n)/(1024.0*1024.0*1024.0)))
      println("%.3f secs".format(s/repeats))
    }

    test("DIABLO Multiply",() => testMultiplyDiablo())
    //test("MLlib Multiply",() => testMultiplyMLlib())

    sc.stop()
  }
}
