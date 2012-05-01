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

formulae(_, [], []) :- !.

formulae(M, [Y : P | T], [Ps | Formulae]) :-
    (atom(P); P = _ sf _), !,
    findall(P, member(u <= Y, M), Ys),
    findall(A says P, member(s(u, A, Y), M), SYs),
    append(Ys, SYs, YsSYs), list_to_set(YsSYs, Ps),
    formulae(M, T, Formulae).

formulae(M, [_ | T], Formulae) :-
    formulae(M, T, Formulae).

formulae(M, Y : P, Ps) :-
    (atom(P); P = _ sf _), !,
    findall(P, member(u <= Y, M), Ys),
    findall(A says P, member(s(u, A, Y), M), SYs),
    append(Ys, SYs, YsSYs), list_to_set(YsSYs, Ps).

formulae(_, _, []).
