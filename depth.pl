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

depth(T, 0) :-
    atom(T), !.

depth(T, D) :-
    T =.. [F, L, R],
    depth(L, DL),
    depth(R, DR),
    (member(F, [says, ->]) -> D is max(DL, DR) + 1; D is max(DL, DR)).

max_depth(D, MD) :-
    MD_ is exp(D), MD__ is exp(MD_), MD___ is exp(MD__), MD is exp(MD___).
