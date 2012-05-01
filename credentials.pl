/*

   Copyright 2012 Daniele Rispoli, Valerio Genovese, Deepak Garg

   This file is part of smart-rsync.

   smart-rsync is free software: you can redistribute it and/or modify
   it under the terms of the GNU Affero General Public License as
   published by the Free Software Foundation, either version 3 of the
   License, or (at your option) any later version.

   smart-rsync is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Affero General Public License for more details.

   You should have received a copy of the GNU Affero General Public
   License along with smart-rsync.  If not, see <http://www.gnu.org/licenses/>.

*/

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
