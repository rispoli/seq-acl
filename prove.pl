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
:- dynamic(lazy/0).
:- dynamic(non_provable/0).

inf2pre(PandorQ, Pre) :-
    PandorQ =.. [Functor | [P | Q]],
    !, inf2pre(P, P_),
    ((P_ =.. [Functor | P_a], !); P_a = [P_]),
    append(P_a, Q, Pre_a),
    Pre =.. [Functor | Pre_a].
inf2pre(P, P) :-
    atom(P).

dnf(F, DNF) :-
    inf2pre(F, F_p),
    dnf_(F_p, DNF).
dnf_(A says P, A says P).
dnf_(P, P) :-
    atom(P), !.
dnf_(F, DNF) :-
    F =.. [Functor | Args],
    maplist(dnf_, Args, Args_DNF),
    ((Functor = (or)) ->
        (!, DNF =.. [Functor | Args_DNF]);
        (findall(P and Q, (member(OPs, Args_DNF), member(OQs, Args_DNF), OPs \= OQs, ((OPs =.. [or | Ps], !); Ps = [OPs]), ((OQs =.. [or | Qs], !); Qs = [OQs]), member(P, Ps), member(Q, Qs)), PsAndQs),
        delete_comm(PsAndQs, PsAndQs, PsAndQs_),
        foldl(or_ab, false_ab, PsAndQs_, DNF))).

delete_comm([], L, L).
delete_comm([P and Q | _], L, L_) :-
    select(Q and P, L, L__), !,
    delete_comm(L__, L__, L_).
delete_comm([_ | T], L, L_) :-
    delete_comm(T, L, L_).

prove(F, Abducibles) :-
    prove(F, 10000000, Abducibles).

prove(F, Max_Depth, Abducibles) :-
    %depth(F, D),
    %max_depth(Depth, Max_Depth),
    assert(lazy),
    retractall(non_provable), reset_gensym,
    r_sequents(u : F, ([u], [u <= u], [], [], [], []), Max_Depth, [], Abducibles_),
    ((Abducibles_ \= true_ab) ->
        (assert(non_provable), dnf(Abducibles_, Abducibles));
        Abducibles = []).

prove(F) :-
    prove(F, _), \+non_provable.
