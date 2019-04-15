% Solving N queens as a SAT problem (finding all solutions)
% We convert the chessboard to a SAT formula by representing each position as a proposition.
% Each requirement of the chessboard is modeled as a propositional clause Qn which is true if
%  there is a queen at position n and false if there is no queen on that position.
%
% Rules of N-Queens:
%   No more than one queen per row.
%   No more than one queen per column.
%   No more than one queen per diagonal.
%
% Each rule can be modeled by a set of propositional clauses applying to a set of positions:
%   For each pair of distinct positions in the set, add the clause "not Q1 or not Q2" to the set.
%
% Thus, given N, we use this algorithm to generate the set of propositional clauses in DIMACS CNF:
%   Row rule:
%       Add the clause "X1 X2 ..." containing every position in the row
%       For Y = 0 to N-1:
%           For X1 = 1 to N-1
%               For X2 = X1+1 to N:
%                   Add the clause "-(Y*N + X1) -(Y*N + X2)"
%   Column rule:
%       For X = 1 to N:
%           For Y1 = 0 to N-2
%               For Y2 = Y1+1 to N-1:
%                   Add the clause "-(X + Y1*N) -(X + Y2*N)"
%   Diagonal rule: 
%   Generate positions in the same diagonal depending on the direction of the diagonal (/ or \) by 
%    adding (N+1) or (N-1) respectively from a starting position on the top row
%    or subtracting (N+1) or (N-1) respectively from a starting position on the bottom row.
%       (/ direction)
%       For Y = 1 to N:
%           For D1 = 0 to N-Y:
%               For D2 = D1+1 to N-Y:
%                   Add the clause "-(Y + D1(N+1)) -(Y + D2(N+1))"
%       For Y = 1 to N-1:
%           For D1 = 0 to Y-1:
%               For D2 = D1+1 to Y-1:
%                   Add the clause "-(N(N-1)+Y - D1(N+1)) -(N(N-1)+Y - D2(N+1))"
%       (\ direction) 
%       For Y = 1 to N:
%           For D1 = 0 to Y-1:
%               For D2 = D1+1 to Y-1:
%                   Add the clause "-(Y + D1(N-1)) -(Y + D2(N-1))"
%       For Y = 2 to N:
%           For D1 = 0 to N-Y:
%               For D2 = D1+1 to N-Y:
%                   Add the clause "-(N(N-1)+Y - D1(N-1)) -(N(N-1)+Y - D2(N-1))"

% Utility Predicates %

% gen(+S, +E, ?L) succeeds for integers S and E where S<E and list L when
% L contains every integer between S and E inclusive.
gen(S, E, L) :-
    S < E,
    L = [S|T],
    N is S+1,
    gen(N, E, T).
gen(E, E, [E]).

% nrow(+N, +R, ?Q) succeeds for integers N, R and queen position Q when 
% Q lies on the Rth row of the N-board.
nrow(N, R, Q) :-
    S is (R - 1)*N + 1,
    E is R*N,
    gen(S, E, L),
    member(Q, L).

% Row rule %
nqRows(N, Y, L) :-
    Y >= 0,
    NP is N-1,
    rowExcl(N, Y, NP, N, Excl),
    NY is Y-1,
    nqRows(N, NY, Acc),
%   Add the clause "X1 X2 ..." containing every position in the row
    S is Y*N + 1,
    E is (Y+1)*N,
    gen(S, E, OrClause),
    append(Acc, [OrClause], Cat),
    append(Cat, Excl, L).
nqRows(_, Y, []) :-
    Y < 0.
nqRows(N, L) :-
    T is N-1,
    nqRows(N, T, L).

rowExcl(N, Y, X1, X2, [C|T]) :-
    X1 > 0,
    ((X2 >= N,
        XP is X1-1, rowExcl(N, Y, XP, X1, T));
        XN is X2+1, rowExcl(N, Y, X1, XN, T)),
    P1 is -(Y*N + X1),
    P2 is -(Y*N + X2),
    C = [P1,P2].
rowExcl(_, _, 0, _, []).


% Column rule %
nqCols(N, X, L) :-
    X > 0,
    Y1 is N-2,
    Y2 is N-1,
    colExcl(N, X, Y1, Y2, Excl),
    NX is X-1,
    nqCols(N, NX, Acc),
    append(Acc, Excl, L).
nqCols(_, 0, []).
nqCols(N, L) :-
    nqCols(N, N, L).

colExcl(N, X, Y1, Y2, [C|T]) :-
    Y1 >= 0,
    ((Y2 >= N-1,
        YP is Y1-1, colExcl(N, X, YP, Y1, T));
        YN is Y2+1, colExcl(N, X, Y1, YN, T)),
    P1 is -(Y1*N + X),
    P2 is -(Y2*N + X),
    C = [P1,P2].
colExcl(_, _, Y1, _, []) :-
    Y1 < 0.


% Diagonal rule %
nqDiag(N, D) :-
    diagURB(N, URB),
    diagURT(N, URT),
    diagULB(N, ULB),
    diagULT(N, ULT),
    append(URB, URT, Cat1),
    append(Cat1, ULB, Cat2),
    append(Cat2, ULT, D).

% *Upper *Right direction
% from *Bottom row:
diagURB(N, Y, L) :-
    Y > 0,
    Y1 is N-Y-1,
    Y2 is N-Y,
    urbExcl(N, Y, Y1, Y2, Excl),
    NY is Y-1,
    diagURB(N, NY, Acc),
    append(Acc, Excl, L).
diagURB(_, 0, []).
diagURB(N, L) :-
    diagURB(N, N, L).

urbExcl(N, Y, D1, D2, [C|T]) :-
    D1 >= 0,
    ((D2 >= N-Y,
        DP is D1-1, urbExcl(N, Y, DP, D1, T));
        DN is D2+1, urbExcl(N, Y, D1, DN, T)),
    P1 is -(Y + D1*(N+1)),
    P2 is -(Y + D2*(N+1)),
    C = [P1,P2].
urbExcl(_, _, D1, _, []) :-
    D1 < 0.

% from *Top row:
diagURT(N, Y, L) :-
    Y > 0,
    Y1 is Y-2,
    Y2 is Y-1,
    urtExcl(N, Y, Y1, Y2, Excl),
    NY is Y-1,
    diagURT(N, NY, Acc),
    append(Acc, Excl, L).
diagURT(_, 0, []).
diagURT(N, L) :-
    NP is N-1,
    diagURT(N, NP, L).

urtExcl(N, Y, D1, D2, [C|T]) :-
    D1 >= 0,
    ((D2 >= Y-1,
        DP is D1-1, urtExcl(N, Y, DP, D1, T));
        DN is D2+1, urtExcl(N, Y, D1, DN, T)),
    P1 is -(Y + N*(N-1) - D1*(N+1)),
    P2 is -(Y + N*(N-1) - D2*(N+1)),
    C = [P1,P2].
urtExcl(_, _, D1, _, []) :-
    D1 < 0.

% *Upper *Left direction
% from *Bottom row:
diagULB(N, Y, L) :-
    Y > 0,
    Y1 is Y-2,
    Y2 is Y-1,
    ulbExcl(N, Y, Y1, Y2, Excl),
    NY is Y-1,
    diagULB(N, NY, Acc),
    append(Acc, Excl, L).
diagULB(_, 0, []).
diagULB(N, L) :-
    diagULB(N, N, L).

ulbExcl(N, Y, D1, D2, [C|T]) :-
    D1 >= 0,
    ((D2 >= Y-1,
        DP is D1-1, ulbExcl(N, Y, DP, D1, T));
        DN is D2+1, ulbExcl(N, Y, D1, DN, T)),
    P1 is -(Y + D1*(N-1)),
    P2 is -(Y + D2*(N-1)),
    C = [P1,P2].
ulbExcl(_, _, D1, _, []) :-
    D1 < 0.

% from *Top row:
diagULT(N, Y, L) :-
    Y > 1,
    Y1 is N-Y-1,
    Y2 is N-Y,
    ultExcl(N, Y, Y1, Y2, Excl),
    NY is Y-1,
    diagULT(N, NY, Acc),
    append(Acc, Excl, L).
diagULT(_, 1, []).
diagULT(N, L) :-
    diagULT(N, N, L).

ultExcl(N, Y, D1, D2, [C|T]) :-
    D1 >= 0,
    ((D2 >= N-Y,
        DP is D1-1, ultExcl(N, Y, DP, D1, T));
        DN is D2+1, ultExcl(N, Y, D1, DN, T)),
    P1 is -(Y + N*(N-1) - D1*(N-1)),
    P2 is -(Y + N*(N-1) - D2*(N-1)),
    C = [P1,P2].
ultExcl(_, _, D1, _, []) :-
    D1 < 0.

% Body predicate using subprocedures to generate clauses for each rule
nqClauses(N, L) :-
    nqRows(N, R),
    nqCols(N, C),
    nqDiag(N, D),
    append(R, C, Cat),
    append(Cat, D, L).

% Main predicate
nqueensFile(N, F) :-
    P is N*N,
    term_string(P, PS),
    string_concat("p cnf ", PS, Cat1),
    string_concat(Cat1, " ", Str),
    term_string(N, NS),
    string_concat("nqueen.", NS, FB),
    string_concat(FB, ".0", FN),
    nqClauses(N, L), !,
    open(FN, write, F),
    write(F, Str),
    writeDimacs(L, F),
    close(F),
    nqueensItr(N, 0, L).

% nqueensItr(+N, +ID, +L) takes integers N (number of queens) and ID (iteration number) and the SAT formula L, 
% finding all solutions to the N queens problem by iteratively eliminating each solution produced.
nqueensItr(N, ID, L) :-
    term_string(N, NS),
    term_string(ID, IDS),
    string_concat("nqueen.", NS, Cat1),
    string_concat(Cat1, ".", NB),
    string_concat(NB, IDS, FN),
    string_concat(FN, ".sat", ON),
    minisat(FN, ON),
    open(ON, read, OF),
    readSoln(S, OF),
    close(OF),
    S \= [],
    convSoln(S, C),
    LN = [C|L],

    P is N*N,
    term_string(P, PS),
    string_concat("p cnf ", PS, Cat),
    string_concat(Cat, " ", Str),
    IDN is ID+1,
    term_string(IDN, IDNS),
    string_concat(NB, IDNS, NF),
    open(NF, write, F),
    write(F, Str),
    writeDimacs(LN, F),
    close(F),
    nqueensItr(N, IDN, LN).


% writeDimacs(+L, +F) writes the list of propositional clauses L to the file F in DIMACS format.
writeDimacs(L, F) :-
    length(L, Len),
    term_string(Len, LS),
    writeln(F, LS),
    writeClauses(L, F).

% writeClauses(+L, +F) writes the propositional clauses in L to the file F.
writeClauses([C|T], F) :-
    writeProps(C, F),
    writeClauses(T, F).
writeClauses([], _).

% writeProps(+C, +F) writes the propositional clause C to the file F.
writeProps([P|T], F) :-
    term_string(P, PS),
    string_concat(PS, " ", Str),
    write(F, Str),
    writeProps(T, F).
writeProps([], F) :-
    writeln(F, "0").

% minisat(+IN, +ON) runs MiniSAT on the file name IN and sends the output to the file named ON.
minisat(IN, ON) :-
    string_concat("minisat ", IN, Cat1),
    string_concat(Cat1, " ", Cat2),
    string_concat(Cat2, ON, Command),
    sh(Command).

% readSoln(-L, +F) reads a DIMACS CNF solution (produced by MiniSAT) from the file F 
% and converts it into the list of terms L.
% L=[] if there is no solution.
readSoln(L, F) :-
    read_string(F, end_of_line, _, H),
    (H = "UNSAT", L = [], !);
    read_string(F, end_of_line, _, S),
    split_string(S, " ", "", SL),
    parseSoln(SL, L).

% parseSoln(+L, -Soln) parses the list of terms L into a simplified list Soln by removing the negated terms.
parseSoln([HS|ST], [H|LT]) :-
    term_string(H, HS),
    H > 0,
    parseSoln(ST, LT).
parseSoln([HS|ST], L) :-
    term_string(H, HS),
    H < 0,
    parseSoln(ST, L).
parseSoln(["0"], []).

% convSoln(+L, -N) converts the list of positive terms L into the negated list N, 
% becoming a propositional clause which will eliminate this solution from the SAT formula.
convSoln([P|T], [N|NT]) :-
    N is -P,
    convSoln(T, NT).
convSoln([], []).
