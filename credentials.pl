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

pretty_print_c(A says P) :-
    !, format('~w', [A says P]) .
pretty_print_c(P and Q) :-
    !, format('~w][~w', [P, Q]).
pretty_print_c(A) :-
    atom(A), write(A).
pretty_print_cs([L]) :-
    !, write('['), pretty_print_c(L), write(']').
pretty_print_cs([H | T]) :-
    !, write('['), pretty_print_c(H), write('];'),
    pretty_print_cs(T).
pretty_print_d(A says P) :-
    !, format('[~w]', [A says P]) .
pretty_print_d(Atom) :-
    atom(Atom), !,
    format('[~w]', [Atom]).
pretty_print_d(Or) :-
    Or =.. [or | Args],
    pretty_print_cs(Args).
pretty_print([]) :-
    !, write('{}').
pretty_print(Abducibles) :-
    write('{'), inf2pre(Abducibles, Abducibles_), pretty_print_d(Abducibles_), write('}').

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
