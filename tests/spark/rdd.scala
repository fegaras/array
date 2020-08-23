import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.rdd.RDD
import edu.uta.array._

case class Tiled[T] ( rows: Int, cols: Int, tiles: RDD[((Int,Int),Array[T])] )

object Test {
  def main(args: Array[ String ]) {
    val conf = new SparkConf().setAppName("rdd")
    val sc = new SparkContext(conf)

    val P = sc.parallelize(1 to 100)
    val R = sc.parallelize(1 to 100)

    val S = sc.parallelize((1 to 100).map( i => (i,i*10.0) ))
    val T = sc.parallelize((1 to 100).map( i => (i,i*10.0) ))
    val Q = sc.parallelize((1 to 100).map( i => (i,i*10.0) ))

    val X = ar("""
       //rdd[ i+j | i <- P, j <- R, i == j ]

       //rdd[ (i,a+1) | (i,a) <- S ]

       //rdd[ (i,a+b) | (i,a) <- S, (j,b) <- T, i == j ]

       rdd[ (i,+/a,+/b) | (i,a) <- S, (j,b) <- T, i == j, group by i ]

       //rdd[ (i,a+b*c) | (i,a) <- S, (j,b) <- T, (l,c) <- Q, i == j, l == i ]

       //rdd[ (k,+/i,*/i) | i <- R, k = i%10, group by k ]

       // nested RDD foreach: rdd[ (i,+/[ j | j <- R, i%10 == j%10 ]) | i <- R ]
    """)

    X.foreach(println)

  }
}
