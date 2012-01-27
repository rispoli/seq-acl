path([], _, _, _) :-
    !, fail.

path(L, U, X, [U <= X]) :-
    member(U <= X, L),
    U \= X.

path(L, U, X, [s(U, A, X)]) :-
    member(s(U, A, X), L).

path(L, U, X, [P | P_]) :-
    (
        (select(Y <= X, L, L_), P = (Y <= X));
        (select(s(Y, A, X), L, L_), P = s(Y, A, X))
    ),
    X \= Y,
    path(L_, U, Y, P_).

all_leq([]).

all_leq([s(_, _, _) | _]) :- !, fail.

all_leq([_ | T]) :-
    all_leq(T).

every_path(L, U, X, Ps) :-
    findall(P_, path(L, U, X, P_), PsRE),
    exclude(all_leq, PsRE, PsR),
    maplist(reverse, PsR, Ps).

formula(Bottom, [], Bottom) :- !.

formula(Bottom, [_ <= _ | T], Formula) :-
    !, formula(Bottom, T, Formula).

formula(Bottom, [s(_, A, _) | T], A says Formula) :-
    formula(Bottom, T, Formula).

formulae(_, [], []) :- !.

formulae(M, [X : Y | T], [Formulae_X | Formulae]) :-
    every_path(M, u, X, Paths),
    maplist(formula(Y), Paths, Formulae_XL),
    list_to_set(Formulae_XL, Formulae_X),
    formulae(M, T, Formulae).
