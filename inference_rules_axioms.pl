:- op(500, yfx, and),
   op(600, yfx, or),
   op(650, xfy, says),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

axiom(M, Γ, Δ, '\\mbox{init}') :-
    member(X <= Y, M),
    member(X : P, Γ),
    member(Y : P, Δ),
    atom(P).

axiom(_, _, Δ, '\\top\\mbox{R}') :-
    member(_ : '\\top', Δ).

axiom(_, Γ, _, '\\bot\\mbox{L}') :-
    member(_ : '\\bot', Γ).

% mon-S
inference_rule_sem((Σ, M, Γ, Δ), [(Σ, [s(X, A, W) | M], Γ, Δ)], '\\mbox{mon-S}') :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+member(s(X, A, W), M).

% ∧: right
inference_rule_r(X : Alpha and Beta, (Σ, M, Γ, Δ), _, [(Σ, M, Γ, [X : Alpha | Δ]), (Σ, M, Γ, [X : Beta | Δ])], '\\land\\mbox{R}').

% ∨: right
inference_rule_r(X: Alpha or Beta, (Σ, M, Γ, Δ), _, [(Σ, M, Γ, [X : Alpha, X : Beta | Δ])], '\\lor\\mbox{R}').

% →: right
inference_rule_r(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, [([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ])], '\\rightarrow\\mbox{R}') :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth.

% says: right
inference_rule_r(X : A says Alpha, (Σ, M, Γ, Δ), Depth, [([Y | Σ], [s(X, A, Y) | M], Γ, [Y : Alpha | Δ])], '\\mbox{\\textsf{says} R}') :-
    gensym(y_, Y),
    max_distance(M, u, X, Distance),
    Distance =< Depth.

% ∧: left
inference_rule_l(X : Alpha and Beta, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [X : Alpha, X : Beta | Γ_], Δ)], '\\land\\mbox{L}') :-
    delete(Γ, X : Alpha and Beta, Γ_).

% ∨: left
inference_rule_l(X : Alpha or Beta, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [X : Alpha | Γ_], Δ), (Σ, M, [X : Beta | Γ_], Δ)], '\\lor\\mbox{L}') :-
    delete(Γ, X : Alpha or Beta, Γ_).

% →: left
inference_rule_l(X : Alpha -> Beta, (Σ, M, Γ, Δ), Used, [(X : Alpha -> Beta, Y) | Used], [(Σ, M, [Y : Beta | Γ], Δ), (Σ, M, Γ, [Y : Alpha | Δ])], '\\rightarrow\\mbox{L}') :-
    member(X <= Y, M),
    \+member(Y : Alpha, Δ),
    \+member(Y : Beta, Γ),
    \+member((X : Alpha -> Beta, Y), Used).

% says: left
inference_rule_l(X : A says Alpha, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [Y : Alpha | Γ], Δ)], '\\mbox{\\textsf{says} L}') :-
    member(s(X, A, Y), M),
    \+member(Y : Alpha, Γ).

% Refl
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [X <= X | M], Γ, Δ)], '\\mbox{Refl}') :-
    member(X, Σ),
    \+member(X <= X, M).

% Trans
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [X <= Z | M], Γ, Δ)], '\\mbox{Trans}') :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+member(X <= Z, M).

% s-I-SS
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [s(X, A, Z) | M], Γ, Δ)], '\\mbox{s-I-SS}') :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+member(s(X, A, Z), M).

% C
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [s(Y, A, Y) | M], Γ, Δ)], '\\mbox{s-C}') :-
    member(s(_, A, Y), M),
    \+member(s(Y, A, Y), M).
