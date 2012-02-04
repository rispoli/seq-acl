foldr(_, Z, [], Z) :- !.

foldr(F, Z, [X | XS], O_) :-
    foldr(F, Z, XS, F_O),
    C =.. [F, X, O],
    C,
    union(O, F_O, O_).

principals(P, [P]) :-
    atom(P), !.

principals(F, P) :-
    F =.. [_ | Args],
    foldr(principals, [], Args, P).

f_principals(F, P) :-
    F =.. [Fn | Args],
    ((Fn = says) ->
        (Args = [Ps, _],
        principals(Ps, P));
        ((Fn = sf) ->
            P = Args;
            foldr(f_principals, [], Args, P))).

set_principals([], []).

set_principals([H | T], P) :-
    f_principals(H, P_H),
    set_principals(T, P_T),
    union(P_H, P_T, P).
