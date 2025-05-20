package util

object Extensions:
  extension [A](xs: Seq[A])
    def subsets: Seq[Set[A]] =
      val n = xs.length
      (0 until (1 << n)).map { i =>
        (0 until n).filter(j => (i & (1 << j)) != 0).map(xs(_)).toSet
      }

  extension [A](xs: Set[A])
    def findDefined[B](f: A => Option[B]): Option[B] =
      var res = Option.empty[B]
      val it = xs.iterator
      while res.isEmpty && it.hasNext do
        res = f(it.next())
      res