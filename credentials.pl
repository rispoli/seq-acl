:- [prove].
:- [grounder].

stringConcat([], Output, Output).

stringConcat([H | T], TempString, Output) :-
    format(atom(H_), '~w', H),
    string_concat(TempString, H_, TempString_),
    stringConcat(T, TempString_, Output).

inner_join([], _, _, '').

inner_join([Last], _, TempString, Output) :-
    format(atom(L), '~w', Last),
    string_concat(TempString, L, Output).

inner_join([H | T], Separator, TempString, Output) :-
    stringConcat([H, Separator], TempString, TempString_),
    inner_join(T, Separator, TempString_, Output).

join_(List, Separator, Output) :-
    inner_join(List, Separator, '', Output), !.

pretty_print__([L]) :-
    !, pretty_print_(L).

pretty_print__([H | T]) :-
    pretty_print_(H),
    write(';'),
    pretty_print__(T).

pretty_print_(L) :-
    is_list(L), !,
    partition(is_list, L, Inner_lists, Inner_atoms),
    ((Inner_lists = []) ->
        (write('['), join_(Inner_atoms, ';', O), write(O), write(']'));
        pretty_print__(Inner_lists)).

pretty_print_(X) :-
    format('~w', X).

pretty_print([]) :-
    !, write('{}').

pretty_print(Abducibles) :-
    write('{'), maplist(pretty_print_, Abducibles), write('}').

prove_c(Policy_F, Principal, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    prove((Policy) -> (Request), Abducibles),
    (non_provable ->
        pretty_print(Abducibles);
        write(granted)).

prove_c(Policy_F, Principal, Credentials, Request) :-
    smart_grounder(Policy_F, Principal, Request, Policy),
    ((Policy = []) ->
        prove((Credentials) -> (Request), Abducibles);
        prove(((Policy) and (Credentials)) -> (Request), Abducibles)),
    (non_provable ->
        pretty_print(Abducibles);
        write(granted)).
