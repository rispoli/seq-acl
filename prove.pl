:- [inference_rules].
:- [depth_distance].
:- [countermodel].
:- dynamic(non_provable/0).

empty([]).

cook_abducibles((_, M, _, _, Δ, _), [Abducibles]) :-
    !, formulae(M, Δ, Abducibles_E), exclude(empty, Abducibles_E, Abducibles).

cook_abducibles([], []).

cook_abducibles([(_, M, _, _, Δ, _) | T], Abducibles) :-
    !, formulae(M, Δ, Abducibles_H_E), exclude(empty, Abducibles_H_E, Abducibles_H),
    cook_abducibles(T, Abducibles_T),
    ((Abducibles_H = []) ->
        Abducibles = Abducibles_T;
        append(Abducibles_H, Abducibles_T, Abducibles)).

cook_abducibles([H | T], [Abducibles_H | Abducibles_T]) :-
    is_list(H),
    cook_abducibles(H, Abducibles_H),
    cook_abducibles(T, Abducibles_T).

prove(F, Abducibles) :-
    depth(F, D),
    retractall(non_provable), reset_gensym,
    prove(([u], [u <= u], [], [], [u : F], []), D, [], Countermodels),
    ((Countermodels \= empty) ->
        (assert(non_provable), cook_abducibles(Countermodels, Abducibles));
        Abducibles = []).

prove(F) :-
    prove(F, _), \+non_provable.
