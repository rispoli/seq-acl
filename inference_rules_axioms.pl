:- op(500, yfx, and),
   op(600, yfx, or),
   op(650, xfy, says),
   op(650, xfy, ratified),
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

% mon-C
inference_rule_sem((Σ, M, Γ, Δ), [(Σ, [c(X, A, W) | M], Γ, Δ)], '\\mbox{mon-C}') :-
    member(X <= Y, M),
    member(c(Y, A, Z), M),
    member(Z <= W, M),
    \+member(c(X, A, W), M).

% mon-R
inference_rule_sem((Σ, M, Γ, Δ), [(Σ, [r(X, A, W) | M], Γ, Δ)], '\\mbox{mon-R}') :-
    member(X <= Y, M),
    member(r(Y, A, Z), M),
    member(Z <= W, M),
    \+member(r(X, A, W), M).

% mon-P
inference_rule_sem((Σ, M, Γ, Δ), [(Σ, [p(W, A, X) | M], Γ, Δ)], '\\mbox{mon-P}') :-
    member(X <= Y, M),
    member(p(Z, A, Y), M),
    member(Z <= W, M),
    \+member(p(W, A, X), M).

% ∧: right
inference_rule_r(X : Alpha and Beta, (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : Alpha | Δ]), (Σ, M, Γ, [X : Beta | Δ])], '\\land\\mbox{R}').

% ∨: right
inference_rule_r(X: Alpha or Beta, (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : Alpha, X : Beta | Δ])], '\\lor\\mbox{R}').

% →: right
inference_rule_r(X : Alpha -> Beta, (Σ, M, Γ, Δ), [([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ])], '\\rightarrow\\mbox{R}') :-
    gensym(y_, Y).

% says: right
inference_rule_r(X : A says Alpha, (Σ, M, Γ, Δ), [([Y | Σ], [s(X, A, Y) | M], Γ, [Y : Alpha | Δ])], '\\mbox{\\textsf{says} R}') :-
    gensym(y_, Y).

% C: right
inference_rule_r(X : c(A, Alpha), (Σ, M, Γ, Δ), [([Y | Σ], [c(X, A, Y) | M], Γ, [Y : Alpha | Δ])], '\\mbox{{\\bf C}R}') :-
    gensym(y_, Y).

% ratified: right
inference_rule_r(X : A ratified Alpha, (Σ, M, Γ, Δ), [([Y | Σ], [r(X, A, Y) | M], Γ, [Y : Alpha | Δ])], '\\mbox{\\textsf{ratified} R}') :-
    gensym(y_, Y).

% P: right
inference_rule_r(X : p(A, Alpha), (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : p(A, Alpha), Y : Alpha | Δ])], '\\mbox{{\\bf P}R}') :-
    member(p(X, A, Y), M),
    \+member(Y : Alpha, Δ).

% ∧: left
inference_rule_l(X : Alpha and Beta, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [X : Alpha, X : Beta | Γ_], Δ)], '\\land\\mbox{L}') :-
    delete(Γ, X : Alpha and Beta, Γ_).

% ∨: left
inference_rule_l(X : Alpha or Beta, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [X : Alpha | Γ_], Δ), (Σ, M, [X : Beta | Γ_], Δ)], '\\lor\\mbox{L}') :-
    delete(Γ, X : Alpha or Beta, Γ_).

% →: left
inference_rule_l(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, [(X : Alpha -> Beta, Y) | Used], [(Σ, M, [Y : Beta | Γ], Δ), (Σ, M, Γ, [Y : Alpha | Δ])], '\\rightarrow\\mbox{L}') :-
    member(X <= Y, M),
    \+member(Y : Alpha, Δ),
    \+member(Y : Beta, Γ),
    \+member((X : Alpha -> Beta, Y), Used),
    max_distance(M, u, Y, Distance),
    Distance =< Depth.

% says: left
inference_rule_l(X : A says Alpha, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [Y : Alpha | Γ], Δ)], '\\mbox{\\textsf{says} L}') :-
    member(s(X, A, Y), M),
    \+member(Y : Alpha, Γ).

% C: left
inference_rule_l(X : c(A, Alpha), (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [Y : Alpha | Γ], Δ)], '\\mbox{{\\bf C}L}') :-
    member(c(X, A, Y), M),
    \+member(Y : Alpha, Γ).

% ratified: left
inference_rule_l(X : A ratified Alpha, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [Y : Alpha | Γ], Δ)], '\\mbox{\\textsf{ratified} L}') :-
    member(r(X, A, Y), M),
    \+member(Y : Alpha, Γ).

% P: left
inference_rule_l(X : p(A, Alpha), (Σ, M, Γ, Δ), _, Used, Used, [([Y | Σ], [p(X, A, Y) | M], [Y : Alpha | Γ_], Δ)], '\\mbox{{\\bf P}L}') :-
    gensym(y_, Y),
    delete(Γ, X : p(A, Alpha), Γ_).

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

% s-del-C
inference_rule((Σ, M, Γ, Δ), Depth, Principals, Used, [c(X, B, Y) | Used], [(Σ, [c(X, A, Y) | M], Γ, Δ), ([Z | Σ], [s(X, A, Z), c(Z, B, Y) | M], Γ, Δ)], '\\mbox{s-del-C}') :-
    member(c(X, B, Y), M),
    \+member(c(X, B, Y), Used),
    member(A, Principals),
    gensym(z_, Z),
    max_distance(M, u, X, Distance),
    Distance =< Depth.

% s-RS
inference_rule((Σ, M, Γ, Δ), _, _, Used, Used, [(Σ, [r(X, A, Y) | M], Γ, Δ)], '\\mbox{s-RS}') :-
    member(s(X, A, Y), M),
    \+member(r(X, A, Y), M).

% s-C2P
inference_rule((Σ, M, Γ, Δ), Depth, Principals, Used, Used, [([Y | Σ], [c(X, A, Y), p(X, A, Y) | M], Γ, Δ)], '\\mbox{s-C2P}') :-
    gensym(y_, Y),
    member(X, Σ),
    member(A, Principals),
    max_distance(M, u, X, Distance),
    Distance =< Depth,
    \+member(c(X, A, _), M),
    \+member(p(X, A, _), M).
