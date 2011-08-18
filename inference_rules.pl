:- op(450, xfy, says),
   op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

% ⊤ R
r_sequents(_ : top, _, _, _, []) :- !.

% says R
r_sequents(X : A says G, (Σ, M, Γ, Ξ), Depth, Used, Abducibles) :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth,
    !, r_sequents(Y : G, ([Y | Σ], [s(X, A, Y) | M], Γ, Ξ), Depth, Used, Abducibles).

% ∧ R
r_sequents(X : G1 and G2, (Σ, M, Γ, Ξ), Depth, Used, Abducibles) :-
    !, r_sequents(X : G1, (Σ, M, Γ, Ξ), Depth, Used, Abducibles_G1),
    r_sequents(X : G2, (Σ, M, Γ, Ξ), Depth, Used, Abducibles_G2),
    append(Abducibles_G1, Abducibles_G2, Abducibles).

% ∨ R
r_sequents(X : G1 or G2, (Σ, M, Γ, Ξ), Depth, Used, Abducibles) :-
    !, r_sequents(X : G1, (Σ, M, Γ, Ξ), Depth, Used, Abducibles_G1),
    ((Abducibles_G1 = []) ->
        Abducibles = [];
        (r_sequents(X : G2, (Σ, M, Γ, Ξ), Depth, Used, Abducibles_G2),
        ((Abducibles_G2 = []) ->
            Abducibles = [];
            append(Abducibles_G1, Abducibles_G2, Abducibles)))).

% → R
r_sequents(X : N -> G, (Σ, M, Γ, Ξ), Depth, Used, Abducibles) :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth,
    !, expand_l_sequents(([Y | Σ], [X <= Y | M], Γ, [Y : N | Ξ], Y : G), Depth, Used, Abducibles).

% atom
r_sequents(X : P, (Σ, M, Γ, []), Depth, Used, Abducibles) :-
    !, expand_sat_sequents(Σ, M, Σ_S, M_S),
    n_sequents((Σ_S, M_S, Γ, X : P), Depth, Used, Abducibles).

% ⊤ L
l_sequents(_ : top, (Σ, M, Γ, Ξ, WG), (Σ, M, Γ, Ξ, WG)).

% ⊥ L
l_sequents(_ : bot, _, _) :- fail.

% ∧ L
l_sequents(X : N1 and N2, (Σ, M, Γ, Ξ, WG), (Σ, M, Γ, [X : N1, X : N2 | Ξ], WG)).

% ∨: left
l_sequents(X : N1 or N2, (Σ, M, Γ, Ξ, WG), [(Σ, M, Γ, [X : N1 | Ξ], WG), (Σ, M, Γ, [X : N2 | Ξ], WG)]).

% pr
l_sequents(X : D, (Σ, M, Γ, Ξ, WG), (Σ, M, [X : D | Γ], Ξ, WG)) :-
    D \= bot.

% L2R
expand_l_sequents((Σ, M, Γ, [], WG), Depth, Used, Abducibles) :-
    !, r_sequents(WG, (Σ, M, Γ, []), Depth, Used, Abducibles).

expand_l_sequents((Σ, M, Γ, Ξ, WG), Depth, Used, Abducibles) :-
    select(X, Ξ, Ξ_X),
    l_sequents(X, (Σ, M, Γ, Ξ_X, WG), Result), !,
    (is_list(Result) ->
        ([L, R] = Result, expand_l_sequents(L, Depth, Used, Abducibles_L), expand_l_sequents(R, Depth, Used, Abducibles_R), append(Abducibles_L, Abducibles_R, Abducibles));
        expand_l_sequents(Result, Depth, Used, Abducibles)).

expand_l_sequents((Σ, M, Γ, Ξ, WG), _, _, (Σ, M, Γ_, WG)) :-
    append(Γ, Ξ, Γ_).

% s-mon
sat_sequents(Σ, M, Σ, [s(X, A, W) | M]) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M).

% refl
sat_sequents(Σ, M, Σ, [X <= X | M]) :-
    member(X, Σ),
    \+memberchk(X <= X, M).

% trans
sat_sequents(Σ, M, Σ, [X <= Z | M]) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M).

% S-C
sat_sequents(Σ, M, Σ, [s(Y, A, Y) | M]) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M).

% S-I
sat_sequents(Σ, M, Σ, [s(X, A, Z) | M]) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M).

expand_sat_sequents(Σ, M, Σ_S, M_S) :-
    sat_sequents(Σ, M, Σ_S_I, M_S_I), !,
    expand_sat_sequents(Σ_S_I, M_S_I, Σ_S, M_S).

expand_sat_sequents(Σ, M, Σ, M).

% init
f_sequents(X : P, (_, M, W : P), Used, Used, []) :-
    member(X <= W, M).

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

get_abducibles([], success, []) :- !.

get_abducibles(AG1Gn, failure, AG1Gn_) :-
    (length(AG1Gn, 1) ->
        nth0(0, AG1Gn, AG1Gn_);
        (maplist(nth0(0), AG1Gn, AG1Gn__), AG1Gn_ = [AG1Gn__])).

nd_choice([], _, _, _, Status, Status, []).

% choice - left branch successful
nd_choice([H | T], (Σ, M, Γ, WP), Depth, Used, _, StatusU, Abducibles) :-
    f_sequents(H, (Σ, M, WP), Used, Used_, G1Gn), !,
    maplist(n2r((Σ, M, Γ, []), Depth, [H | Used_]), G1Gn, AG1Gn),
    subtract(AG1Gn, [[]], AG1Gn_NonEmpty),
    get_abducibles(AG1Gn_NonEmpty, StatusH, Abducibles_H),
    ((StatusH = success) ->
        StatusU = StatusH;
        (nd_choice(T, (Σ, M, Γ, WP), Depth, Used, failure, StatusU, Abducibles_T), append(Abducibles_H, Abducibles_T, Abducibles))).

% choice - left branch unsuccessful
nd_choice([_ | T], (Σ, M, Γ, WP), Depth, Used, _, Status, Abducibles) :-
    nd_choice(T, (Σ, M, Γ, WP), Depth, Used, failure, Status, Abducibles).

n_sequents((Σ, M, Γ, WP), Depth, Used, Abducibles) :-
    subtract(Γ, Used, Γ_),
    nd_choice(Γ_, (Σ, M, Γ, WP), Depth, Used, failure, Status, Abducibles_ND),
    ((Status = success) ->
        Abducibles = [];
        Abducibles = [(Σ, M, Γ, WP) | Abducibles_ND]).

n2r(Context, Depth, Used, WiGi, AWiGi) :-
    r_sequents(WiGi, Context, Depth, Used, AWiGi).
