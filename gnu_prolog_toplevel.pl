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

:- initialization(prove_c).
:- include('credentials').

a2t(A, T) :-
    atom_concat(A, '.', A_),
    read_from_atom(A_, T).

prove_c :-
    argument_counter(N),
    ((N == 4) ->
        (argument_list([PF, P, R_]), a2t(R_, R), prove_c(PF, P, R));
        ((N == 5) ->
            (argument_list([PF, P, C_, R_]), a2t(C_, C), a2t(R_, R), prove_c(PF, P, C, R));
            print('Usage:\n\tcredentials.gnu <policy_file> principal request\n or:\n\tcredentials.gnu <policy_file> principal credentials request\n'))).
