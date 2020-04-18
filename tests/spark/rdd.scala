import org.apache.spark.SparkContext
import org.apache.spark.SparkConf
import org.apache.spark.rdd.RDD
import edu.uta.array._

case class Tiled[T] ( rows: Int, cols: Int, tiles: RDD[((Int,Int),Array[T])] )

object Test {
  def main(args: Array[ String ]) {
    val conf = new SparkConf().setAppName("rdd")
    val sc = new SparkContext(conf)

    val R = sc.parallelize(1 to 100)

    val S = ar("""
       //rdd[ i+j | i <- R, j <- R, i == j ]

       rdd[ (k,+/i) | i <- R, k = i%10, group by k ]

       // nested => error: rdd[ (i,+/[ j | j <- R, i%10 == j%10 ]) | i <- R ]
    """)

    S.foreach(println)

  }
}
