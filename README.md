# NqueensMiniSAT
N queens: How to place N queens on an N x N chessboard without any pair of them lying on the same row, column or diagonal.

This project is split into two parts:

* nqueens.pl: Solving the problem directly using Prolog
* nqueensDIMACS.pl: Converting the problem to a set of propositional clauses in DIMACS CNF format which can then be interpreted and solved by a SAT solver (MiniSAT in this case).
  * As MiniSAT only produces one solution for a satisfiable set of clauses, the program is also able to read, parse and eliminate the solution produced before calling MiniSAT again to generate another solution. This continues until all solutions are found.

This project was done for an assignment for CS3234 (Logic and Formal Systems). As part of the restrictions imposed by the assignment, the Constraint Logic Programming features of ECLiPSe Prolog (the dialect used) were not used at all.

## Setup

To use this program:

1. Clone the repository or download the source files.
2. Install [ECLiPSe Prolog](http://eclipseclp.org/) and [MiniSAT](http://minisat.se/). This program was written and tested on ECLiPSe Prolog 7.0 and may not necessarily work on any other version of ECLiPSe or dialect of Prolog (eg. SWI).
3. Compile the source files into ECLiPSe.
4. Run the main predicates, `nqueens(+N, ?L)` and `nqueensFile(+N, -F)`.
