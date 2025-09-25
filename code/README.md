
## code

Small implementation of different SAT solvers in Scala. Not much attention has
been paid to performance.

[`src/main/scala/theories/Bool.scala`](src/main/scala/theories/Bool.scala)
defines the formulas.

[`src/main/scala/theories/Theory.scala`](src/main/scala/theories/Theory.scala)
defines the notion of a theory.

[`src/main/scala/solvers/Solver.scala`](src/main/scala/solvers/Solver.scala)
defines a solver interface, a simple SAT solver, and a DPLL (and DPLL(T))
implementation.

[`src/main/scala/solvers/CDCL.scala`](src/main/scala/solvers/CDCL.scala)
defines a CDCL(T) implementation and in principle produces proofs, but this is
not well tested.

There is a non-working in-progress LRA theory implementation, which is the only
use of the dependencies as well.
