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

foldr(_, Z, [], Z) :- !.

foldr(F, Z, [X | XS], O_) :-
    foldr(F, Z, XS, F_O),
    C =.. [F, X, O],
    C,
    union(O, F_O, O_).

principals(P, [P]) :-
    atom(P), !.

principals(F, P) :-
    F =.. [_ | Args],
    foldr(principals, [], Args, P).

f_principals(F, P) :-
    F =.. [Fn | Args],
    ((Fn = says) ->
        (Args = [Ps, _],
        principals(Ps, P));
        ((Fn = sf) ->
            P = Args;
            foldr(f_principals, [], Args, P))).

set_principals([], []).

set_principals([H | T], P) :-
    f_principals(H, P_H),
    set_principals(T, P_T),
    union(P_H, P_T, P).
