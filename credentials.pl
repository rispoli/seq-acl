:- [deduction_tree].
:- [countermodel].

empty([]).

empty([ _ ]) :- !, fail.

print_leaves(([(_, M, _, Δ), []], '')) :-
    formulae(M, Δ, XE),
    exclude(empty, XE, XF),
    flatten(XF, X),
    write(X).

print_leaves(([_, Premises], _)) :-
    maplist(print_leaves, Premises).

prove_c(Policy, Request) :-
    prove((Policy) -> (Request), T),
    (non_provable ->
        print_leaves(T);
        write(granted)).

prove_c(Policy, Credentials, Request) :-
    prove(((Policy) and (Credentials)) -> (Request), T),
    (non_provable ->
        print_leaves(T);
        write(granted)).
