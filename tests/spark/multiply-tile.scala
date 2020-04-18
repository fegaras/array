import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.rdd.RDD
import scala.util.Random
import Math._
import edu.uta.array._


object MultiplySpark {
  def main(args: Array[ String ]) {
    val conf = new SparkConf().setAppName("Multiply")
    val sc = new SparkContext(conf)

    val N = 100
    val M = N
    val n = 400
    val m = n

    case class Tile ( tile: Array[Double] ) {
      def add ( that: Tile ): Tile
        = Tile(ar("array(N*N)[ (i,x+y) | (i,x) <- tile, (j,y) <- that.tile, i == j ]"))
    }

    case class Tiled ( rows: Int, cols: Int, tiles: RDD[((Int,Int),Tile)] )

    def randomMatrix ( n: Int, m: Int ): RDD[((Int,Int),Double)] = {
      val max = 10
      val l = Random.shuffle((0 until n).toList)
      val r = Random.shuffle((0 until m).toList)
      sc.parallelize(l)
        .flatMap{ i => val rand = new Random()
                       r.map{ j => ((i.toInt,j.toInt),rand.nextDouble()*max) } }
        .cache()
    }

    def toArray ( l: Iterable[(Int,Double)] ): Array[Double]
      = ar("array(N*N)[ v[i] | (i,v) <- l ]")

    def toTiled ( matrix: RDD[((Int,Int),Double)] ): Tiled
      = Tiled( n, m, matrix.map{ case ((i,j),v) => ((i/N,j/N),((i%N)*N+(j%N),v)) }
                           .groupByKey
                           .mapValues(a => Tile(toArray(a)))
                           .cache() )

    def toTiled2 ( matrix: RDD[((Int,Int),Double)] ): Tiled
      = ar("""
           Tiled( n, m, rdd[ ((i/N,j/N),Tile(array(N*N)[ v[i] | (i,v) <- iv ]))
                           | v[i,j] <- matrix, iv = ((i%N)*N+(j%N),v),
                             group by (i,j) ] )
           """)

    val MC = randomMatrix(n,m)
    val NC = randomMatrix(n,m)
    val MT = toTiled(MC)
    val NT = toTiled(NC)

    def multiply ( X: Tile, Y: Tile ): Tile
      = Tile(ar("""
                array(N*N)[ (k,+/v) | x[i] <- X.tile, y[j] <- Y.tile,
                                      i%N == j/N, v = x*y,
                                      group by k: i/N*N+j/N ]
                """))

    val S = ar("""
       Tiled( n, m, rdd[ ( (i,j), v.reduce(add) )
                       | a[i,k] <- MT.tiles,
                         b[kk,j] <- NT.tiles,
                         kk == k, v = multiply(a,b),
                         group by (i,j)  ] )
       """)

    println(S.tiles.count)

    sc.stop()
  }
}
