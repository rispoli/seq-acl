:- [prove].
:- [grounder].

pretty_print__(A) :-
    is_list(A) ->
        format('~w', [A]);
        format('~w', [[A]]).

pretty_print_([L]) :-
    partition(is_list, L, Premises, Consequent), Premises \= [], !,
    format('~w', [Consequent]),
    nth0(0, Premises, Premises_), maplist(pretty_print__, Premises_).

pretty_print_([L]) :-
    !, format('~w', [L]).

pretty_print_([H | T]) :-
    partition(is_list, H, Premises, Consequent), Premises \= [], !,
    format('~w;', [Consequent]),
    nth0(0, Premises, Premises_), maplist(pretty_print__, Premises_),
    pretty_print_(T).

pretty_print_([H | T]) :-
    format('~w;', [H]),
    pretty_print_(T).

pretty_print([]) :-
    !, write('{}').

pretty_print(Abducibles) :-
    write('{'), pretty_print_(Abducibles), write('}').

prove_c(Policy_F, Principal, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    prove((Policy) -> (Request), Abducibles),
    (non_provable ->
        pretty_print(Abducibles);
        write(granted)).

prove_c(Policy_F, Principal, Credentials, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    prove(((Policy) and (Credentials)) -> (Request), Abducibles),
    (non_provable ->
        pretty_print(Abducibles);
        write(granted)).
