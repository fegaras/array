import org.apache.spark._
import org.apache.spark.rdd._
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
    val operation = args(0).toInt
    val repeats = args(1).toInt
    val n = args(2).toInt
    val m = n
    val N = args(3).toInt

    val conf = new SparkConf().setAppName("tiles")
    val sc = new SparkContext(conf)
    conf.set("spark.logConf","false")
    conf.set("spark.eventLog.enabled","false")
    LogManager.getRootLogger().setLevel(Level.WARN)

    def randomMatrix ( n: Int, m: Int ): RDD[((Int,Int),Double)] = {
      val max = 10
      val l = Random.shuffle((0 until n).toList)
      val r = Random.shuffle((0 until m).toList)
      sc.parallelize(l)
        .flatMap{ i => val rand = new Random()
                       r.map{ j => ((i.toInt,j.toInt),rand.nextDouble()*max) } }
        .cache()
    }

    def mtoString ( x: RDD[((Int,Int),Double)] ): String = {
      var res = ""
      val z = x.collect().toMap
      for ( i <- 0 until n ) {
          for ( j <- 0 until m )
              res = res+"\t"+(if (z.contains((i,j)))  "%.2f".format(z((i,j))) else 0.0)
          res = res+"\n"
      }
      res
    }

    case class Tiled ( rows: Int, cols: Int, tiles: RDD[((Int,Int),Array[Double])] ) {
      override def toString (): String
        = tiles.map(_._1).collect().map(_.toString).reduce(_+_) + "\n" + mtoString(toIJV(this))
    }

    def toArray ( l: Iterable[(Int,Double)] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { (i,v) <- l if i >=0 if i < V.length } V(i) = v
       V
    }

    def toTiled ( matrix: RDD[((Int,Int),Double)] ): Tiled
      = Tiled( n, m, matrix.map{ case ((i,j),v) => ((i/N,j/N),((i%N)*N+(j%N),v)) }
                           .groupByKey
                           .mapValues(toArray)
                           .cache() )

    def toIJV ( matrix: Tiled ): RDD[((Int,Int),Double)]
      = matrix.tiles.flatMap{ case ((ii,jj),a) => (0 until N*N).map{ i => ((ii*N+i/N,jj*N+i%N),a(i)) } }

    def multiply ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- 0 until N }
           for { j <- 0 until N }
               for { k <- 0 until N }
                   V(i*N+j) += x(i*N+k)*y(k*N+j)
       V
    }

    def add ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- 0 until N*N }
           V(i) = x(i)+y(i)
       V
    }

    def multiplyP ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N*N).par }
           V(i) = x(i)*y(i)
       V
    }

    def addP ( x: Array[Double], y: Array[Double] ): Array[Double] = {
       val V = Array.ofDim[Double](N*N)
       for { i <- (0 until N*N).par }
           V(i) = x(i)+y(i)
       V
    }

    val MC = randomMatrix(n,m)
    val NC = randomMatrix(n,m)
    val MT = toTiled(MC)
    val NT = toTiled(NC)

    def testAddIJV (): Double = {
      val t: Long = System.currentTimeMillis()

      try {
        val R = MC.join(NC)
                  .map{ case (k,(a,b)) => (k,a+b) }

        val c = R.count
      } catch { case x: Throwable => println(x) }

      (System.currentTimeMillis()-t)/1000.0
    }

    def testAdd (): Double = {
      val t: Long = System.currentTimeMillis()

      try {

        val S = Tiled( n, m, MT.tiles.join(NT.tiles)
                              .map{ case ((ii,jj),(a,b))
                                      => val V = Array.ofDim[Double](N*N);
                                         for { i <- 0 until min(MT.rows,NT.rows);
                                               j <- 0 until min(NT.cols,NT.cols)
                                               if ii == i/N && jj == j/N  }
                                            V((i%N)*N+(j%N)) = a( (i%N)*N+(j%N) ) + b( (i%N)*N+(j%N) );
                                         ( (ii, jj), V )
                                  }
                              .cache() )

        val c = S.tiles.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testAddPar (): Double = {
      val t: Long = System.currentTimeMillis()

      try {

        val S = Tiled( n, m, MT.tiles.join(NT.tiles)
                              .map{ case ((ii,jj),(a,b))
                                      => val V = Array.ofDim[Double](N*N);
                                         for { i <- (0 until min(MT.rows,NT.rows)).par;
                                               j <- 0 until min(MT.cols,NT.cols)
                                               if ii == i/N && jj == j/N  }
                                            V((i%N)*N+(j%N)) = a( (i%N)*N+(j%N) ) + b( (i%N)*N+(j%N) );
                                         ( (ii, jj), V )
                                  }
                              .cache() )

        val c = S.tiles.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testMultiplyIJV (): Double = {
      val t: Long = System.currentTimeMillis()

      try {
        val R = MC.map{ case ((i,j),m) => (j,(i,m)) }
                  .join( NC.map{ case ((i,j),n) => (i,(j,n)) } )
                  .map{ case (k,((i,m),(j,n))) => ((i,j),m*n) }
                  .reduceByKey(_+_)
 
        val c = R.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testMultiply (): Double = {
      val t: Long = System.currentTimeMillis()

      try {

        val S = Tiled( n, m, MT.tiles.map{ case ((i,k),a) => (k,(i,a)) }
                               .join( NT.tiles.map{ case ((kk,j),b) => (kk,(j,b)) } )
                               .map{ case (_,((i,a),(j,b))) => ((i,j),multiply(a,b)) }
                               .reduceByKey(add).cache() )

        val c = S.tiles.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def testMultiplyPar (): Double = {
      val t: Long = System.currentTimeMillis()

      try {

        val S = Tiled( n, m, MT.tiles.map{ case ((i,k),a) => (k,(i,a)) }
                            .join( NT.tiles.map{ case ((kk,j),b) => (kk,(j,b)) } )
                            .map{ case (_,((i,a),(j,b))) => ((i,j),multiplyP(a,b)) }
                            .reduceByKey(addP).cache() )

        val c = S.tiles.count
      } catch { case x: Throwable => println(x) }
      (System.currentTimeMillis()-t)/1000.0
    }

    def test ( name: String, f: () => Double ) {
      val cores = Runtime.getRuntime().availableProcessors()
      val s = (for ( i <- 1 to repeats ) yield f()).sum
      print("*** %s cores=%d n=%d N=%d %.2f GB ".format(name,cores,n,N,(8.0*n.toDouble*m)/(1024.0*1024.0*1024.0)))
      println("%.3f secs".format(s/repeats))
    }

    operation match {
       case 1 => test("AddIJV",testAddIJV)
       case 2 => test("Add",testAdd)
       case 3 => test("AddPar",testAddPar)
       case 4 => test("MultiplyIJV",testMultiplyIJV)
       case 5 => test("Multiply",testMultiply)
       case 6 => test("MultiplyPar",testMultiplyPar)
       case _ =>;
    }

    sc.stop()
  }
}
