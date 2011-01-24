:- op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

axiom(M, Γ, Δ, 'init') :-
    member(X <= Y, M),
    member(X : P, Γ),
    member(Y : P, Δ),
    atom(P).

axiom(_, _, Δ, '\\top R') :-
    member(_ : '\\top', Δ).

axiom(_, Γ, _, '\\bot L') :-
    member(_ : '\\bot', Γ).

% ∧: right
inference_rule_r(X : Alpha and Beta, (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : Alpha | Δ]), (Σ, M, Γ, [X : Beta | Δ])], '\\land R').

% ∨: right
inference_rule_r(X: Alpha or Beta, (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : Alpha, X : Beta | Δ])], '\\lor R').

% ⊃: right
inference_rule_r(X : Alpha -> Beta, (Σ, M, Γ, Δ), [([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ])], '\\supset R') :-
    gensym(y_, Y).

% □: right
inference_rule_r(X : [](I, Alpha), (Σ, M, Γ, Δ), [([Y | Σ], [n(X, I, Y) | M], Γ, [Y : Alpha | Δ])], '\\square_i R') :-
    gensym(y_, Y).

% ◊: right
inference_rule_r(X : <>(I, Alpha), (Σ, M, Γ, Δ), [(Σ, M, Γ, [X : <>(I, Alpha), Y : Alpha | Δ])], '\\lozenge_i R') :-
    member(p(X, I, Y), M),
    \+member(Y : Alpha, Δ).

% ∧: left
inference_rule_l(X : Alpha and Beta, (Σ, M, Γ, Δ), [(Σ, M, [X : Alpha, X : Beta | Γ], Δ)], '\\land L').

% ∨: left
inference_rule_l(X : Alpha or Beta, (Σ, M, Γ, Δ), [(Σ, M, [X : Alpha | Γ], Δ), (Σ, M, [X : Beta | Γ], Δ)], '\\lor L').

% ⊃: left
inference_rule_l(X : Alpha -> Beta, (Σ, M, Γ, Δ), [(Σ, M, Γ, [Y : Alpha | Δ]), (Σ, M, [Y : Beta | Γ], Δ)], '\\supset L') :-
    member(X <= Y, M),
    \+member(Y : Beta, Γ),
    \+member(Y : Alpha, Δ).

% □: left
inference_rule_l(X : [](I, Alpha), (Σ, M, Γ, Δ), [(Σ, M, [Y : Alpha | Γ], Δ)], '\\square_i L') :-
    member(n(X, I, Y), M),
    \+member(Y : Alpha, Γ).

% ◊: left
inference_rule_l(X : <>(I, Alpha), (Σ, M, Γ, Δ), [([Y | Σ], [p(X, I, Y) | M], [Y : Alpha | Γ], Δ)], '\\lozenge_i R') :-
    gensym(y_, Y).

% Unit
inference_rule((Σ, M, Γ, Δ), [(Σ, [X <= Y | M], Γ, Δ)], 'Unit') :-
    member(n(X, _, Y), M),
    \+member(X <= Y, M).

% Refl
inference_rule((Σ, M, Γ, Δ), [(Σ, [X <= X | M], Γ, Δ)], 'Refl') :-
    member(X, Σ),
    \+member(X <= X, M).

% Trans
inference_rule((Σ, M, Γ, Δ), [(Σ, [X <= Z | M], Γ, Δ)], 'Trans') :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+member(X <= Z, M).

% □: monotonicity
inference_rule((Σ, M, Γ, Δ), [(Σ, [n(X, I, W) | M], Γ, Δ)], '\\square_i monotonicity') :-
    member(X <= Y, M),
    member(n(Y, I, Z), M),
    member(Z <= W, M),
    \+member(n(X, I, W), M).

% ◊: monotonicity
inference_rule((Σ, M, Γ, Δ), [(Σ, [p(W, I, X) | M], Γ, Δ)], '\\lozenge_i monotonicity') :-
    member(X <= Y, M),
    member(p(Z, I, Y), M),
    member(Z <= W, M),
    \+member(p(W, I, X), M).

% C
inference_rule((Σ, M, Γ, Δ), [(Σ, [n(Y, I, Y) | M], Γ, Δ)], 'C') :-
    member(n(_, I, Y), M),
    \+member(n(Y, I, Y), M).
