filter(_, [], []) :- !.

filter(P, [H | T], [H | R]) :-
    call(P, H), !,
    filter(P, T, R).

filter(P, [_ | T], R) :-
    filter(P, T, R).

maplist(Goal, List) :-
    maplist_(List, Goal).

maplist_([], _).
maplist_([Elem|Tail], Goal) :-
    call(Goal, Elem),
    maplist_(Tail, Goal).

maplist(Goal, List1, List2) :-
    maplist_(List1, List2, Goal).

maplist_([], [], _).
maplist_([Elem1|Tail1], [Elem2|Tail2], Goal) :-
    call(Goal, Elem1, Elem2),
    maplist_(Tail1, Tail2, Goal).

flag(Sym, Old, NewExp) :-
    g_read(Sym, Old),
        nonvar(NewExp) ->
            New is NewExp,
            g_assign(Sym, New)
            ;
            g_read(Sym, New).

gensym(Base, Atom) :-
    atom_concat('gs_', Base, Key),
    flag(Key, N, N+1),
    number_atom(N, NA),
    atom_concat(Base, NA, Atom), !.

exclude(Goal, List, Included) :-
    exclude_(List, Goal, Included).

exclude_([], _, []).
exclude_([X1|Xs1], P, Included) :-
    (   call(P, X1)
    ->  Included = Included1
    ;   Included = [X1|Included1]
    ),
    exclude_(Xs1, P, Included1).

partition(Pred, List, Included, Excluded) :-
    partition_(List, Pred, Included, Excluded).

partition_([], _, [], []).
partition_([H|T], Pred, Incl, Excl) :-
    (   call(Pred, H)
    ->  Incl = [H|I],
        partition_(T, Pred, I, Excl)
    ;   Excl = [H|E],
        partition_(T, Pred, Incl, E)
    ).

union([], L, L) :- !.
union([H|T], L, R) :-
    memberchk(H, L), !,
    union(T, L, R).
union([H|T], L, [H|R]) :-
    union(T, L, R).
