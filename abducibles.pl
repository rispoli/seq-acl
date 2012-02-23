formulae(_, [], []) :- !.

formulae(M, [Y : P | T], [Ps | Formulae]) :-
    (atom(P); P = _ sf _), !,
    findall(P, member(u <= Y, M), Ys),
    findall(A says P, member(s(u, A, Y), M), SYs),
    append(Ys, SYs, YsSYs), list_to_set(YsSYs, Ps),
    formulae(M, T, Formulae).

formulae(M, [_ | T], Formulae) :-
    formulae(M, T, Formulae).
