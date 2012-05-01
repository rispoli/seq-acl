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

:- op(450, xfx, controls),
   op(450, xfx, trusts),
   op(450, yfx, on).

and([L], X, X and L) :- !.

and([H | T], X, T_A) :-
    and(T, X and H, T_A).

and([], []).

and([X], X) :- !.

and([H | T], T_A) :-
    and(T, H, T_A).

same_cons([], _, [], Ls, Ls) :- !.

same_cons([L_ -> R | T], R, T_, L, Ls) :-
    !, same_cons(T, R, T_, L or L_, Ls).

same_cons([H | T], R, [H | T_], L, Ls) :-
    same_cons(T, R, T_, L, Ls).

same_ant([], _, [], Rs, Rs) :- !.

same_ant([L -> R_ | T], L, T_, R, Rs) :-
    !, same_ant(T, L, T_, R and R_, Rs).

same_ant([H | T], L, [H | T_], R, Rs) :-
    same_ant(T, L, T_, R, Rs).

collapse([], []).

collapse([L -> R | T], [Collapsed_Head | Collapsed_Tail]) :-
    (
        (same_ant(T, L, T_, R, Rs), R \= Rs, Collapsed_Head = (L -> Rs));
        (same_cons(T, R, T_, L, Ls), L \= Ls, Collapsed_Head = (Ls -> R));
        (T_ = T, Collapsed_Head = (L -> R))
    ), !,
    collapse(T_, Collapsed_Tail).

collapse([H | T], [H | CT]) :-
    collapse(T, CT).

translate_controls_trusts(A controls P, A says P -> P) :- !.

translate_controls_trusts(A trusts B on P, A says (B says P -> P)) :- !.

translate_controls_trusts(Formula, Translated_Formula) :-
    Formula =.. [F | Args],
    maplist(translate_controls_trusts, Args, Translated_Args),
    Translated_Formula =.. [F | Translated_Args].

controls(Formulae, Principal, Request, P controls Request) :-
    memberchk(_ -> P trusts Principal on Request, Formulae).

is_cons(Request, _, _, _, _ -> Request) :- !.

is_cons(Request, _, _, _, Request) :- !.

is_cons(Request, Formulae, Principal, Request, _ -> P trusts Principal on Request) :-
    memberchk(P controls Request, Formulae).

is_cons(X, _, _, _, _ -> Y) :-
    \+functor(X, and, _), !,
    Y =.. [or | Ys],
    \+intersection([X], Ys, []).

is_cons(X, _, _, _, _ -> Y) :-
    X =.. [and | Xs],
    \+functor(Y, or, _), !,
    \+intersection(Xs, [Y], []).

is_cons(X, _, _, _, _ -> Y) :-
    X =.. [and | Xs],
    Y =.. [or | Ys],
    \+intersection(Xs, Ys, []).

is_cons(X, _, _, _, Y) :-
    X =.. [and | Xs],
    \+intersection(Xs, [Y], []).

filter(L, Principal, Request, X -> Y, [X -> Y | O]) :-
    !, include(is_cons(X, L, Principal, Request), L, L_I),
    maplist(filter(L, Principal, Request), L_I, L_M),
    flatten(L_M, O).

filter(_, _, _, X, [X]).

ground_f(Formulae) :-
    findall(F, policy(F), Formulae_F),
    list_to_set(Formulae_F, Formulae).

smart_grounder(Filename, Principal, Request, Formulae) :-
    consult(Filename),
    ground_f(Formulae_G),
    filter(Formulae_G, Principal, Request, Request -> _, [_ | Formulae_F_C]),
    include(controls(Formulae_G, Principal, Request), Formulae_G, Formulae_I),
    append(Formulae_I, Formulae_F_C, Formulae_F),
    maplist(translate_controls_trusts, Formulae_F, Formulae_T),
    collapse(Formulae_T, Formulae_A),
    and(Formulae_A, Formulae).
