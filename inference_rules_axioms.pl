:- op(450, xfy, says),
   op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

axiom(M, Γ, Y : P, '\\mbox{init}') :-
    member(X <= Y, M),
    member(X : P, Γ).

axiom(_, _, _ : '\\top', '\\top\\mbox{R}').

axiom(_, Γ, _, '\\bot\\mbox{L}') :-
    memberchk(_ : '\\bot', Γ).

% mon-S
inference_rule_sem((Σ, M, Γ, Δ), [(Σ, [s(X, A, W) | M], Γ, Δ)], '\\mbox{mon-S}') :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M).

open_leaves(([_, []], '')) :- !.

open_leaves(([_, []], _)) :- !, fail.

open_leaves(([_, P], _)) :-
    \+include(open_leaves, P, []).

in(H1, H2, H) :-
    is_list(H1),
    \+is_list(H2), !,
    in_(H1, [H2], H).

in(H1, H2, H) :-
    \+is_list(H1),
    is_list(H2), !,
    in_([H1], H2, H).

in(H1, H2, H) :-
    in_(H1, H2, H).

in_([], _, []) :- !.

in_([HH1 | TH1], H2, [HH | TH]) :-
    !, in__(H2, HH1, HH),
    in_(TH1, H2, TH).

in_(H1, H2, H) :-
    in___(H1, H2, H).

in__([], _, []).

in__([HH2 | TH2], H1, [HH | TH]) :-
    in___(H1, HH2, HH),
    in__(TH2, H1, TH).

in___(discard, H2, H2).

in___(H1, discard, H1).

in___(([(Σ1, M1, Γ1, Δ1), []], ''), ([(Σ2, M2, Γ2, Δ2), []], ''), ([(Σ, M, Γ, [Δ1, Δ2]), []], '')) :-
    union(Σ1, Σ2, Σ),
    union(M1, M2, M),
    union(Γ1, Γ2, Γ).

% ∧: right
inference_rule_r(X : Alpha and Beta, (Σ, M, Γ, _), _, _, _, [(Σ, M, Γ, X : Alpha), (Σ, M, Γ, X : Beta)], '\\land\\mbox{R}').

% ∨: right
inference_rule_r(X: Alpha or Beta, (Σ, M, Γ, _), Depth, Principals, Used, Premises, '\\lor\\mbox{R}') :-
    search_nodes((Σ, M, Γ, X : Alpha), Depth, Principals, Used, TL),
    (open_leaves(TL) ->
        (search_nodes((Σ, M, Γ, X : Beta), Depth, Principals, Used, TR),
        (open_leaves(TR) ->
            in(TL, TR, Premises);
            (retract(non_provable), Premises = [TR])));
        Premises = [TL]).

% →: right
inference_rule_r(X : Alpha -> Beta, (Σ, M, Γ, _), Depth, _, _, [([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], Y : Beta)], '\\rightarrow\\mbox{R}') :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth.

% says: right
inference_rule_r(X : A says Alpha, (Σ, M, Γ, _), Depth, _, _, [([Y | Σ], [s(X, A, Y) | M], Γ, Y : Alpha)], '\\mbox{\\textsf{says} R}') :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth.

% ∧: left
inference_rule_l(X : Alpha and Beta, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [X : Alpha, X : Beta | Γ_], Δ)], '\\land\\mbox{L}') :-
    delete(Γ, X : Alpha and Beta, Γ_).

% ∨: left
inference_rule_l(X : Alpha or Beta, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [X : Alpha | Γ_], Δ), (Σ, M, [X : Beta | Γ_], Δ)], '\\lor\\mbox{L}') :-
    delete(Γ, X : Alpha or Beta, Γ_).

% says: left
inference_rule_l(X : A says Alpha, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [Y : Alpha | Γ], Δ)], '\\mbox{\\textsf{says} L}') :-
    member(s(X, A, Y), M),
    \+memberchk(Y : Alpha, Γ).

la(_ : _ -> _).

% →: left
inference_rule_la((Σ, M, Γ, Δ), Depth, Principals, Used, Premises, '\\rightarrow\\mbox{L}') :-
    include(la, Γ, Γ_la),
    la_f(Γ_la, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_LA),
    (is_list(Premises_LA) -> Premises = Premises_LA; ((Premises_LA = discard) -> fail; Premises = [Premises_LA])).

lal(X, X <= _).

la_f([], _, _, _, _, discard).

la_f([X : Alpha -> Beta | T], (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    include(lal(X), M, M_lal),
    la_l(M_lal, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_H), !,
    (is_list(Premises_H) ->
        Premises = Premises_H;
        ((retract(non_provable) -> true; true), !, la_f(T, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_T), in(Premises_H, Premises_T, Premises))).

la_l([], _, _, _, _, _, discard).

la_l([X <= Y | T], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    \+memberchk(Y : Beta, Γ),
    \+memberchk((X : Alpha -> Beta, Y), Used), !,
    search_nodes((Σ, M, [Y : Beta | Γ], Δ), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TB),
    (open_leaves(TB) ->
        ((retract(non_provable) -> true; true), !, la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises));
        (search_nodes((Σ, M, Γ, Y : Alpha), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TA),
        (open_leaves(TA) ->
            ((retract(non_provable) -> true; true), !, la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_T), in(TA, Premises_T, Premises));
            Premises = [TB, TA]))).

la_l([_ | T], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises).

% Refl
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [X <= X | M], Γ, Δ)], '\\mbox{Refl}') :-
    member(X, Σ),
    \+memberchk(X <= X, M).

% Trans
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [X <= Z | M], Γ, Δ)], '\\mbox{Trans}') :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M).

% s-I-SS
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [s(X, A, Z) | M], Γ, Δ)], '\\mbox{s-I-SS}') :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M).

% C
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [s(Y, A, Y) | M], Γ, Δ)], '\\mbox{s-C}') :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M).
