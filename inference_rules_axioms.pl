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
    maplist(open_leaves, P).

open_leaves(([_, PL], _) or ([_, PR], _)) :-
    (maplist(open_leaves, PL), !);
    maplist(open_leaves, PR).

% ∧: right
inference_rule_r(X : Alpha and Beta, (Σ, M, Γ, _), _, _, _, [(Σ, M, Γ, X : Alpha), (Σ, M, Γ, X : Beta)], '\\land\\mbox{R}').

% ∨: right
inference_rule_r(X: Alpha or Beta, (Σ, M, Γ, _), Depth, Principals, Used, Premises, '\\lor\\mbox{R}') :-
    search_nodes((Σ, M, Γ, X : Alpha), Depth, Principals, Used, TL),
    (open_leaves(TL) ->
        (search_nodes((Σ, M, Γ, X : Beta), Depth, Principals, Used, TR),
        (open_leaves(TR) ->
            Premises = [TL or TR];
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
inference_rule_la((Σ, M, Γ, Δ), Depth, Principals, Used, Premises, '\\rightarrow\\mbox{L}') :- % [Premises]
    include(la, Γ, Γ_la),
    la_f(Γ_la, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_LA),
    (is_list(Premises_LA) -> Premises = Premises_LA; Premises = [Premises_LA]).

lal(X, X <= _).

la_f([X : Alpha -> Beta], (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    !, include(lal(X), M, M_lal),
    la_l(M_lal, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises).

la_f([X : Alpha -> Beta | T], (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    include(lal(X), M, M_lal),
    la_l(M_lal, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_H),
    (is_list(Premises_H) ->
        Premises = Premises_H;
        (retract(non_provable), !, la_f(T, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_T), (is_list(Premises_T) -> Premises = Premises_T; Premises = Premises_H or Premises_T))).

la_l([X <= Y], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    !, \+memberchk(Y : Beta, Γ),
    \+memberchk((X : Alpha -> Beta, Y), Used),
    search_nodes((Σ, M, Γ, Y : Alpha), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TA),
    (open_leaves(TA) ->
        Premises = TA;
        (search_nodes((Σ, M, [Y : Beta | Γ], Δ), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TB),
        (open_leaves(TB) ->
            Premises = TB;
            Premises = [TA, TB]))).

la_l([X <= Y | T], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises) :-
    \+memberchk(Y : Beta, Γ),
    \+memberchk((X : Alpha -> Beta, Y), Used),
    search_nodes((Σ, M, Γ, Y : Alpha), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TA),
    (open_leaves(TA) ->
        (retract(non_provable), !, la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_T), (is_list(Premises_T) -> Premises = Premises_T; Premises = TA or Premises_T));
        (search_nodes((Σ, M, [Y : Beta | Γ], Δ), Depth, Principals, [(X : Alpha -> Beta, Y) | Used], TB),
        (open_leaves(TB) ->
            (retract(non_provable), !, la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises_T), (is_list(Premises_T) -> Premises = Premises_T; Premises = TB or Premises_T));
            Premises = [TA, TB]))).

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
