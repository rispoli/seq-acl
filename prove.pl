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

:- [inference_rules].
%:- [depth].
:- [abducibles].
:- dynamic(lazy/0).
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
    assert(lazy),
    retractall(non_provable), reset_gensym,
    r_sequents(u : F, ([u], [u <= u], [], [], [], []), Max_Depth, [], Abducibles_),
    ((Abducibles_ \= empty) ->
        (assert(non_provable), cook_abducibles(Abducibles_, Abducibles));
        Abducibles = []).

prove(F) :-
    prove(F, _), \+non_provable.
