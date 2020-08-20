object Test {
  def main ( args: Array[String] ) {
    val n = args(1).toInt
    val A = Array.fill(n)(0)
    var v = 0.0

    println("n = "+n)

    var t = System.currentTimeMillis()
    for ( k <- 0 until 10 )
      for ( i <- 0 until n )
        v = 0.3*A(i)+1.2
    println("for: "+(System.currentTimeMillis()-t)/10000.0)

    v = 0.0
    t = System.currentTimeMillis()
    for ( k <- 0 until 10 ) {
      var i = 0
      while ( i < n ) {
        v = 0.3*A(i)+1.2
        i += 1
      }
    }
    println("while: "+(System.currentTimeMillis()-t)/10000.0)

  }
}
