:- [inference_rules].
:- [depth_distance].
:- [abducibles].
:- [countermodels].
:- dynamic(non_provable/0).

empty([]).

cook_abducibles((Σ, M, Γ, Δ), [Abducibles], [Countermodels]) :-
    !, formulae(M, Δ, Abducibles_E), exclude(empty, Abducibles_E, Abducibles),
    countermodels((Σ, M, Γ, Δ), Countermodels).

cook_abducibles([], [], []).

cook_abducibles([(Σ, M, Γ, Δ) | T], Abducibles, [Countermodels_H | Countermodels_T]) :-
    !, formulae(M, Δ, Abducibles_H_E), exclude(empty, Abducibles_H_E, Abducibles_H),
    countermodels((Σ, M, Γ, Δ), Countermodels_H),
    cook_abducibles(T, Abducibles_T, Countermodels_T),
    ((Abducibles_H = []) ->
        Abducibles = Abducibles_T;
        append(Abducibles_H, Abducibles_T, Abducibles)).

cook_abducibles([H | T], [Abducibles_H | Abducibles_T], [Countermodels_H | Countermodels_T]) :-
    is_list(H),
    cook_abducibles(H, Abducibles_H, Countermodels_H),
    cook_abducibles(T, Abducibles_T, Countermodels_T).

prove(F, Abducibles, Countermodels) :-
    depth(F, D),
    retractall(non_provable), reset_gensym,
    prove(([u], [u <= u], [], [u : F]), D, [], A_C),
    ((A_C \= empty) ->
        (assert(non_provable), cook_abducibles(A_C, Abducibles, Countermodels));
        Abducibles = []).

prove(F, Abducibles) :-
    prove(F, Abducibles, _).

prove(F) :-
    prove(F, _, _), \+non_provable.
