import edu.uta.array._


object Test {
  def main ( args: Array[String] ) {

    val A = Array(1,2,3,4,5,6)

    val x = ar("""

       array{ V => [ (v+w)[i] | v[i] <- V, w[j] <- V, j == i-1, i > 0 ] } A

       """)

    x.foreach(println)

  }
}
