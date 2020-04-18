import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.rdd.RDD
import Math._

case class Tiled[T] ( rows: Int, cols: Int, tiles: RDD[((Int,Int),Array[T])] )

object MultiplySpark {
  def main(args: Array[ String ]) {
    val conf = new SparkConf().setAppName("Multiply")
    val sc = new SparkContext(conf)

    val N = 100
    val M = N
    val n = 10000
    val m = n

    def incr ( S: Tiled[Double] ): Tiled[Double]
      = Tiled( n, m,
               S.tiles.map{ case ((ii,jj),a)
                              => {  val V = Array.ofDim[Double](N*M);
                                    for {  i <- (0 until S.rows).par;
                                           j <- 0 until S.cols
                                           if ii == i/N
                                           if jj == j/M
                                        } V((i%N)*M+(j%M)) = a( (i%N)*M+(j%M) )+1;
                                    ( (ii, jj), V ) }
                          } )

    def add ( A: Tiled[Double], B: Tiled[Double] ): Tiled[Double]
      = Tiled( n, m,
                A.tiles.join(B.tiles)
                 .map{ case ((ii,jj),(a,b))
                         => {  val V = Array.ofDim[Double](N*M);
                               for {  i <- (0 until min(A.rows,B.rows)).par;
                                      j <- 0 until min(A.cols,B.cols)
                                      if ii == i/N
                                      if jj == j/M
                                    } V((i%N)*M+(j%M)) = a( (i%N)*M+(j%M) )+b( (i%N)*M+(j%M) );
                               ( (ii, jj), V ) }
                     } )

    def multiply ( A: Tiled[Double], B: Tiled[Double] ): Tiled[Double]
      = Tiled( n, m,
                A.tiles.join(B.tiles)
                 .map{ case ((ii,jj),(a,b))
                         => {  val V = Array.ofDim[Double](N*M);
                               for {  i <- (0 until min(A.rows,B.rows)).par;
                                      j <- 0 until min(A.cols,B.cols)
                                      if ii == i/N
                                      if jj == j/M
                                    } V((i%N)*M+(j%M)) = a( (i%N)*M+(j%M) )*b( (i%N)*M+(j%M) );
                               ( (ii, jj), V ) }
                     }
                 .reduceByKey{ case (a,b)
                                 => {  val V = Array.ofDim[Double](N*M);
                                       for { i <- 0 until min(a.length,b.length)
                                           } V(i) = a(i)+b(i);
                                       V
                                     } } )



/*
                         => {  val V = Array.ofDim[Double](N*M);
                               for {  i <- (0 until min(A.rows,B.rows)).par;
                                      j <- 0 until min(A.cols,B.cols)
                                    } V((i%N)*M+(j%M)) = a( (i%N)*M+(j%M) )+b( (i%N)*M+(j%M) );
                               V }
                     } )
*/
    sc.stop()
  }
}
