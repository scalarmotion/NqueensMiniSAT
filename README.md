# NqueensMiniSAT
N queens: How to place N queens on an N x N chessboard without any of them threatening each other.

This project is split into two parts:

* Solving the problem directly using Prolog
* Formulating the problem as a set of propositional clauses which can then be interpreted and solved by a SAT solver (MiniSAT in this case).
  * As MiniSAT only produces one solution for a satisfiable set of clauses, the program is also able to read and parse the solution  it produced, then eliminate this solution and call MiniSAT again. This continues until all solutions are found.

This project was done for an assignment for CS3234 (Logic and Formal Systems). As part of the restrictions imposed by the assignment, the Constraint Logic Programming features of Eclipse Prolog (the dialect used) were not used at all.
