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

:- [principals].

:- op(400, xfy, sf),
   op(450, xfy, says),
   op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

:- [abducibles].

and_ab(true_ab, T, T) :- !.
and_ab(T, true_ab, T) :- !.
and_ab(false_ab, _, false_ab) :- !.
and_ab(_, false_ab, false_ab) :- !.
and_ab(T1, T2, T1 and T2).

or_ab(true_ab, _, true_ab) :- !.
or_ab(_, true_ab, true_ab) :- !.
or_ab(false_ab, T, T) :- !.
or_ab(T, false_ab, T) :- !.
or_ab(T1, T2, T1 or T2).

% ⊤ R
r_sequents(_ : top, _, _, _, true_ab) :- !.

% says R
r_sequents(X : A says G, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth, Used, Abducibles) :-
    (Max_Depth > 0; (append(Γ, Γ_S, Γ_), \+loop(X, M, Γ_, [X : A says G | Δ_S]))),
    gensym(y_, Y),
    Max_Depth_ is Max_Depth - 1,
    !, r_sequents(Y : G, ([Y | Σ], [s(X, A, Y) | M], Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles).

% ∧ R
r_sequents(X : G1 and G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth, Used, Abducibles) :-
    Max_Depth > 0,
    Max_Depth_ is Max_Depth - 1,
    !, r_sequents(X : G1, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G1),
    r_sequents(X : G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G2),
    and_ab(Abducibles_G1, Abducibles_G2, Abducibles).

% ∨ R
r_sequents(X : G1 or G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth, Used, Abducibles) :-
    lazy,
    Max_Depth > 0,
    Max_Depth_ is Max_Depth - 1,
    !, r_sequents(X : G1, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G1),
    ((Abducibles_G1 = true_ab) ->
        Abducibles = true_ab;
        (r_sequents(X : G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G2),
        ((Abducibles_G2 = true_ab) ->
            Abducibles = true_ab;
            or_ab(Abducibles_G1, Abducibles_G2, Abducibles)))).

% ∨ R
r_sequents(X : G1 or G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth, Used, Abducibles) :-
    \+lazy,
    Max_Depth > 0,
    Max_Depth_ is Max_Depth - 1,
    !, r_sequents(X : G1, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G1),
    r_sequents(X : G2, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth_, Used, Abducibles_G2),
    or_ab(Abducibles_G1, Abducibles_G2, Abducibles).

% → R
r_sequents(X : N -> G, (Σ, M, Γ, Γ_S, Ξ, Δ_S), Max_Depth, Used, Abducibles) :-
    (Max_Depth > 0; (append(Γ, Γ_S, Γ_), \+loop(X, M, Γ_, [X : N -> G | Δ_S]))),
    gensym(y_, Y),
    Max_Depth_ is Max_Depth - 1,
    !, expand_l_sequents(([Y | Σ], [X <= Y | M], Γ, Γ_S, [Y : N | Ξ], Y : G, Δ_S), Max_Depth_, Used, Abducibles).

% atom
r_sequents(X : P, (Σ, M, Γ, Γ_S, [], Δ_S), Max_Depth, Used, Abducibles) :-
    Max_Depth > 0,
    Max_Depth_ is Max_Depth - 1,
    !, expand_sat_sequents(Σ, M, Γ, X : P, Σ_S, M_S, Γ_Sa),
    n_sequents((Σ_S, M_S, Γ_Sa, Γ_S, X : P, Δ_S), Max_Depth_, Used, Abducibles).

match__([], _, _).

match__([_ : F | T], Δ, Y) :-
    member(Y : F, Δ),
    match__(T, Δ, Y).

match_([], Δ_F, _, Δ, Y) :-
    match__(Δ_F, Δ, Y).

match_([_ : F | T], Δ_F, Γ, Δ, Y) :-
    member(Y : F, Γ),
    match_(T, Δ_F, Γ, Δ, Y).

match([], [X : F | T], _, Δ) :-
    member(Y : F, Δ),
    X \= Y,
    match__(T, Δ, Y).

match([X : F | T], Δ_F, Γ, Δ) :-
    member(Y : F, Γ),
    X \= Y,
    match_(T, Δ_F, Γ, Δ, Y).

ancestors_imp(M, X, Y) :-
    member(Y <= X, M).

ancestors_imp(M, X, Y) :-
    member(W <= X, M),
    ancestors_imp(M, W, Y).

ancestors_says(M, X, Y) :-
    member(Y <= X, M); member(s(Y, _, X), M).

ancestors_says(M, X, Y) :-
    (member(W <= X, M); member(s(W, _, X), M)),
    ancestors_says(M, W, Y).

t(X, M, Γ, X : A says D) :-
    !, ancestors_says(M, X, Y),
    member(Y : A says D, Γ).

t(X, M, Γ, X : G -> D) :-
    !, ancestors_imp(M, X, Y),
    member(Y : G -> D, Γ).

t(X, _, _, X : _).

f(X, X : _).

loop(X, M, Γ, Δ) :-
    include(f(X), Δ, Δ_F),
    include(t(X, M, Γ), Γ, Γ_T),
    match(Γ_T, Δ_F, Γ, Δ).

% ⊤ L
l_sequents(_ : top, _, true_ab).

% ⊥ L
l_sequents(_ : bot, _, _) :- fail.

% ∧ L
l_sequents(X : N1 and N2, (Σ, M, Γ, Γ_S, Ξ, WG, Δ_S), (Σ, M, Γ, [X : N1 and N2 | Γ_S], [X : N1, X : N2 | Ξ], WG, Δ_S)).

% ∨ L
l_sequents(X : N1 or N2, (Σ, M, Γ, Ξ, WG, Δ_S), [(Σ, M, Γ, [X : N1 or N2 | Γ_S], [X : N1 | Ξ], WG, Δ_S), (Σ, M, Γ, [X : N1 or N2 | Γ_S], [X : N2 | Ξ], WG, Δ_S)]).

% pr
l_sequents(X : D, (Σ, M, Γ, Γ_S, Ξ, WG, Δ_S), (Σ, M, [X : D | Γ], Γ_S, Ξ, WG, Δ_S)) :-
    D \= bot.

% L2R
expand_l_sequents((Σ, M, Γ, Γ_S, [], WG, Δ_S), Max_Depth, Used, Abducibles) :-
    !, r_sequents(WG, (Σ, M, Γ, Γ_S, [], Δ_S), Max_Depth, Used, Abducibles).

expand_l_sequents((Σ, M, Γ, Γ_S, Ξ, WG, Δ_S), Max_Depth, Used, Abducibles) :-
    Max_Depth > 0,
    select(X, Ξ, Ξ_X),
    l_sequents(X, (Σ, M, Γ, Γ_S, Ξ_X, WG, Δ_S), Result), !,
    Max_Depth_ is Max_Depth - 1,
    (is_list(Result) ->
        ([L, R] = Result, expand_l_sequents(L, Max_Depth_, Used, Abducibles_L), expand_l_sequents(R, Max_Depth_, Used, Abducibles_R), and_ab(Abducibles_L, Abducibles_R, Abducibles));
        expand_l_sequents(Result, Max_Depth_, Used, Abducibles)).

expand_l_sequents((Σ, M, Γ, Γ_S, Ξ, WG, Δ_S), _, _, (Σ, M, Γ_, Γ_S, WG, Δ_S)) :-
    append(Γ, Ξ, Γ_).

% mon-s
sat_sequents(Σ, M, Γ, _, Σ, [s(X, A, W) | M], Γ) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M).

% refl
sat_sequents(Σ, M, Γ, _, Σ, [X <= X | M], Γ) :-
    member(X, Σ),
    \+memberchk(X <= X, M).

% trans
sat_sequents(Σ, M, Γ, _, Σ, [X <= Z | M], Γ) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M).

% I
sat_sequents(Σ, M, Γ, _, Σ, [s(X, A, Z) | M], Γ) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M).

% sf-refl
sat_sequents(Σ, M, Γ, XP, Σ, M, [X : A sf A | Γ]) :-
    member(X, Σ),
    set_principals([XP | Γ], P),
    member(A, P),
    \+memberchk(X : A sf A, Γ).

% sf
sat_sequents(Σ, M, Γ, _, Σ, [s(X, A, Y) | M], Γ) :-
    member(s(X, B, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(s(X, A, Y), M).

% sf-trans
sat_sequents(Σ, M, Γ, _, Σ, M, [X : A sf C | Γ]) :-
    member(X : A sf B, Γ),
    member(X : B sf C, Γ),
    \+memberchk(X : A sf C, Γ).

% sf-unit
sat_sequents(Σ, M, Γ, _, Σ, M, [Y : A sf B | Γ]) :-
    member(s(X, _, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ).

% sf-mon
sat_sequents(Σ, M, Γ, _, Σ, M, [Y : A sf B | Γ]) :-
    member(X <= Y, M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ).

expand_sat_sequents(Σ, M, Γ, XP, Σ_S, M_S, Γ_Sa) :-
    sat_sequents(Σ, M, Γ, XP, Σ_S_I, M_S_I, Γ_Sa_I), !,
    expand_sat_sequents(Σ_S_I, M_S_I, Γ_Sa_I, XP, Σ_S, M_S, Γ_Sa).

expand_sat_sequents(Σ, M, Γ, _, Σ, M, Γ).

% init
f_sequents(X : P, (_, M, W : P), Used, Used, []) :-
    member(X <= W, M).

% sf
f_sequents(X : A sf B, (_, _, X : A sf B), Used, Used, []).

% ∧ L
f_sequents(X : D1 and D2, (Σ, M, WP), Used, Used_, G1Gn) :-
    f_sequents(X : D1, (Σ, M, WP), Used, Used_, G1Gn);
    f_sequents(X : D2, (Σ, M, WP), Used, Used_, G1Gn).

% → L
f_sequents(X : G -> D, (Σ, M, WP), Used, Used_, [Y : G | G1Gn]) :-
    member(X <= Y, M),
    \+memberchk((X : G -> D, Y), Used),
    f_sequents(Y : D, (Σ, M, WP), [(X : G -> D, Y) | Used], Used_, G1Gn).

% says L
f_sequents(X : A says D, (Σ, M, WP), Used, Used_, G1Gn) :-
    member(s(X, A, Y), M),
    f_sequents(Y : D, (Σ, M, WP), [(X : A says D, Y) | Used], Used_, G1Gn).

nd_choice([], _, _, _, Status, Status, false_ab).

% choice - left branch successful
nd_choice([H | T], (Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth, Used, _, StatusU, Abducibles) :-
    Max_Depth > 0,
    f_sequents(H, (Σ, M, WP), Used, Used_, G1Gn), !,
    Max_Depth_ is Max_Depth - 1,
    maplist(n2r((Σ, M, Γ, Γ_S, [], Δ_S), Max_Depth_, [H | Used_]), G1Gn, AG1Gn),
    foldl(and_ab, true_ab, AG1Gn, Abducibles_H),
    ((Abducibles_H = true_ab) ->
        StatusU = success;
        (nd_choice(T, (Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth_, Used, failure, StatusU, Abducibles_T), or_ab(Abducibles_H, Abducibles_T, Abducibles))).

% choice - left branch unsuccessful
nd_choice([_ | T], (Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth, Used, _, Status, Abducibles) :-
    nd_choice(T, (Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth, Used, failure, Status, Abducibles).

n_sequents((Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth, Used, Abducibles) :-
    subtract(Γ, Used, Γ_),
    nd_choice(Γ_, (Σ, M, Γ, Γ_S, WP, Δ_S), Max_Depth, Used, failure, Status, Abducibles_ND),
    ((Status = success) ->
        Abducibles = true_ab;
        (ab(M, WP, Ab), or_ab(Abducibles_ND, Ab, Abducibles))).

n2r(Context, Max_Depth, Used, WiGi, AWiGi) :-
    r_sequents(WiGi, Context, Max_Depth, Used, AWiGi).
