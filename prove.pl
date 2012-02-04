:- [inference_rules].
%:- [depth].
:- [countermodel].
:- dynamic(non_provable/0).

cook_abducibles((_, M, _, _, WP, _), [Abducibles]) :-
    !, formulae(M, WP, Abducibles).

cook_abducibles([], []).

cook_abducibles([(_, M, _, _, WP, _) | T], Abducibles) :-
    !, formulae(M, WP, Abducibles_H),
    cook_abducibles(T, Abducibles_T),
    ((Abducibles_H = []) ->
        Abducibles = Abducibles_T;
        (is_list(WP) -> append(Abducibles_H, Abducibles_T, Abducibles); Abducibles = [Abducibles_H | Abducibles_T])).

cook_abducibles([H | T], [Abducibles_H | Abducibles_T]) :-
    is_list(H),
    cook_abducibles(H, Abducibles_H),
    cook_abducibles(T, Abducibles_T).

prove(F, Abducibles) :-
    prove(F, 10000000, Abducibles).

prove(F, Max_Depth, Abducibles) :-
    %depth(F, D),
    %max_depth(Depth, Max_Depth),
    retractall(non_provable), reset_gensym,
    r_sequents(u : F, ([u], [u <= u], [], [], [], []), 0, Max_Depth, [], Countermodels),
    ((Countermodels \= empty) ->
        (assert(non_provable), cook_abducibles(Countermodels, Abducibles));
        Abducibles = []).

prove(F) :-
    prove(F, _), \+non_provable.
