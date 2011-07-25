:- [deduction_tree].
:- [grounder].
:- [countermodel].

nested_or(L or R, NO) :-
    !, nested_or(L, NL),
    pretty_print(R, PR),
    format(atom(NO), '~w;~w', [NL, PR]).

nested_or(X, PX) :-
    pretty_print(X, PX).

pretty_print(L or R, PO) :-
    !, nested_or(L, NL),
    pretty_print(R, PR),
    format(atom(PO), '{~w;~w}', [NL, PR]).

pretty_print([], '') :- !.

pretty_print([L, R], PO) :-
    is_list(L), is_list(R), !,
    pretty_print(L, PL),
    pretty_print(R, PR),
    format(atom(PO), '~w~w', [PL, PR]).

pretty_print(L, PL) :-
    is_list(L), !,
    maplist(pretty_print, L, PL).

pretty_print(X, PX) :-
    format(atom(PX), '~w', X).

empty([]).

empty([ _ ]) :- !, fail.

empty_closed_premise(([_, []], Label)) :-
    Label \= ''.

get_result(In, Out) :-
    length(In, 1) ->
        nth0(0, In, Out);
        In = Out.

print_leaves(([(_, M, _, Δ), []], ''), X) :-
    !, formulae(M, Δ, XE),
    exclude(empty, XE, XO),
    get_result(XO, X).

print_leaves(([_, L_Premises], _) or ([_, R_Premises], _), L_Leaves or R_Leaves) :-
    maplist(print_leaves, L_Premises, L_Leaves_FO), get_result(L_Leaves_FO, L_Leaves),
    maplist(print_leaves, R_Premises, R_Leaves_FO), get_result(R_Leaves_FO, R_Leaves).

print_leaves(([_, Premises], _), Leaves) :-
    exclude(empty_closed_premise, Premises, PremisesNE),
    maplist(print_leaves, PremisesNE, LeavesO), get_result(LeavesO, Leaves).

prove_c(Policy_F, Principal, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    prove((Policy) -> (Request), T),
    (non_provable ->
        (print_leaves(T, L), pretty_print(L, PL), write(PL));
        write(granted)).

prove_c(Policy_F, Principal, Credentials, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    prove(((Policy) and (Credentials)) -> (Request), T),
    (non_provable ->
        (print_leaves(T, L), pretty_print(L, PL), write(PL));
        write(granted)).
