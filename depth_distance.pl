depth(T, 0) :-
    atom(T), !.

depth(T, D) :-
    T =.. [F, L, R],
    depth(L, DL),
    depth(R, DR),
    (member(F, [says, ->]) -> D is max(DL, DR) + 1; D is max(DL, DR)).

distance([], _, _, _) :-
    !, fail.

distance(L, U, X, 0) :-
    memberchk(U <= X, L);
    memberchk(s(U, _, X), L).

distance(L, U, X, D) :-
    (
        select(Y <= X, L, L_);
        select(s(Y, _, X), L, L_)
    ),
    X \= Y,
    distance(L_, U, Y, D_),
    D is D_ + 1.

max_distance(L, U, X, D) :-
    findall(D_, distance(L, U, X, D_), Ds),
    max_list(Ds, D).
