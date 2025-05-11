package util

object Extensions:
  extension [A](xs: Seq[A])
    def subsets: Seq[Set[A]] =
      val n = xs.length
      (0 until (1 << n)).map { i =>
        (0 until n).filter(j => (i & (1 << j)) != 0).map(xs(_)).toSet
      }