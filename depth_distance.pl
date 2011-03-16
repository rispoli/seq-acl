depth(T, 1) :-
    atom(T), !.

depth(T, D) :-
    T =.. [F, L, R],
    depth(L, DL),
    depth(R, DR),
    (member(F, [says, ->]) -> D is max(DL, DR) + 1; D is max(DL, DR)).

distance([], _, _, _) :-
    !, fail.

distance(L, U, X, 1) :-
    member(U <= X, L);
    (member(T, L), T =.. [F | As], member(F, [c, p, r, s]), [U, _, X] = As).

distance(L, U, X, D) :-
    (
        select(Y <= X, L, L_);
        (select(T, L, L_), T =.. [F | As], member(F, [c, p, r, s]), [Y, _, X] = As)
    ),
    X \= Y,
    distance(L_, U, Y, D_),
    D is D_ + 1.

max_distance(L, U, X, D) :-
    findall(D_, distance(L, U, X, D_), Ds),
    max_list(Ds, D).
