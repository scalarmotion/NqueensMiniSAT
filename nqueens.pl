% Solving N queens using Eclipse Prolog (no CLP).
%   We use the fact that the queens should be sorted in ascending order and that there 
%   should only be one queen per row to simplify generation which reduces the search space.

% threatens(+R1, +C1, +R2, +C2) succeeds for integers R1, C1, R2, C2 when 
% the queen at (C1, R1) and the queen at (C2, R2) threaten each other (starting at 0).
threatens(R1, C1, R2, C2) :-
    (R1 = R2, !);
    (C1 = C2, !);
    R1 > R2,
    % Q1 is upper right of Q2
    (C1 > C2, X is C1-C2, Y is R1-R2, X=Y, !);
    % Q1 is upper left of Q2
    C2 > C1, X is C2-C1, Y is R1-R2, X=Y.
threatens(R1, C1, R2, C2) :-
    R1 < R2,
    threatens(R2, C2, R1, C1), !.

% sq(+N, +Q, ?R, ?C) succeeds for a queen position Q and integers N, R, C when
% a queen placed at Q is on the Rth row and Cth column (starting from 0).
sq(N, Q, R, C) :-
    R is (Q-1)//N,
    C is mod(Q-1, N).

% bad_queen(+L, +Q, N) succeeds for a list of queen positions L and queen position Q when
% a queen placed at Q is threatened by any queen in L.
bad_queen(L, Q1, N) :-
    member(Q2, L),
    sq(N, Q1, R1, C1),
    sq(N, Q2, R2, C2),
    threatens(R1, C1, R2, C2).

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

% nqueensub(+N, ?L, ?T, +R) succeeds for integers N and R and lists of queen positions L and T
% when T contains valid queens from the last row to the Rth row.
nqueensub(N, L, T, R) :-
    R > 0,
    nrow(N, R, Q),
    NR is R-1,
    not(bad_queen(T, Q, N)),
    nqueensub(N, L, [Q|T], NR).
nqueensub(_, L, L, 0).

% The main predicate.
nqueens(N, L) :-
    nqueensub(N, L, [], N).
