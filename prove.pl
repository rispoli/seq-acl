:- [inference_rules].
:- [depth_distance].
:- [countermodel].
:- dynamic(non_provable/0).

cook_abducibles([], []).

cook_abducibles([(_, M, _, WP) | T], Abducibles) :-
    !, formulae(M, WP, Abducibles_H),
    cook_abducibles(T, Abducibles_T),
    ((Abducibles_H = []) ->
        Abducibles = Abducibles_T;
        Abducibles = [Abducibles_H | Abducibles_T]).

cook_abducibles([H | T], [Abducibles_H | Abducibles_T]) :-
    is_list(H),
    cook_abducibles(H, Abducibles_H),
    cook_abducibles(T, Abducibles_T).

prove(F, Abducibles) :-
    depth(F, D),
    retractall(non_provable), reset_gensym,
    r_sequents(u : F, ([u], [u <= u], [], []), D, [], Abducibles_Ingredients),
    ((Abducibles_Ingredients \= []) ->
        (assert(non_provable), cook_abducibles(Abducibles_Ingredients, Abducibles));
        Abducibles = []).

prove(F) :-
    prove(F, _), \+non_provable.
