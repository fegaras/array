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

    val n = 400
    val m = n

    def randomMatrix ( n: Int, m: Int ): RDD[((Int,Int),Double)] = {
      val max = 10
      val l = Random.shuffle((0 until n).toList)
      val r = Random.shuffle((0 until m).toList)
      sc.parallelize(l)
        .flatMap{ i => val rand = new Random()
                       r.map{ j => ((i.toInt,j.toInt),rand.nextDouble()*max) } }
        .cache()
    }


    val M = randomMatrix(n,m)
    val N = randomMatrix(n,m)

    ar("""
       rdd[ (+/v)[i,j] | m[i,k] <- M, n[kk,j] <- N, v = m*n, k == kk, group by (i,j) ]
    """)

  }
}
