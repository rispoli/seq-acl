:- [principals].

:- op(400, xfy, sf),
   op(450, xfy, says),
   op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

un(empty, empty, empty) :- !.

un(empty, H, [H]) :- !.

un(H, empty, [H]) :- !.

un(H1, H2, [H1, H2]).

% ⊤ R
prove((_, _, _, Δ), _, _, empty) :-
    memberchk(_ : top, Δ), !.

% init
prove((_, M, Γ, Δ), _, _, empty) :-
    member(Y : P, Δ),
    member(X <= Y, M),
    member(X : P, Γ), !.

% ⊥ L
prove((_, _, Γ, _), _, _, empty) :-
    memberchk(_ : bot, Γ).

prove(F, Depth, Used, Abducibles) :-
    expand_r_rules(F, Depth, Used, Abducibles).

expand_r_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X, Δ),
    r_rules(X, (Σ, M, Γ, Δ), Depth, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used, Abducibles_L), prove(R, Depth, Used, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used, Abducibles)).

expand_r_rules(F, Depth, Used, Abducibles) :-
    expand_l_rules(F, Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ, Δ), _, [(Σ, M, Γ, [X : Alpha | Δ]), (Σ, M, Γ, [X : Beta | Δ])]) :-
    \+memberchk(X : Alpha, Δ),
    \+memberchk(X : Beta, Δ).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ, Δ), _, (Σ, M, Γ, [X : Alpha, X : Beta | Δ])) :-
    \+memberchk(X : Alpha, Γ);
    \+memberchk(X : Beta, Γ).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, ([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ])) :-
    findall(Y_, (member(X <= Y_, M), (member(Y_ : Alpha, Γ); member(Y_ : Beta, Δ))), []),
    max_distance(M, u, X, Distance),
    (Distance < Depth; \+loop(X, M, Γ, Δ, _)), !,
    gensym(y_, Y).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Δ), Depth, ([Y | Σ], [s(X, A, Y) | M], Γ, [Y : Alpha | Δ])) :-
    findall(Y_, (member(s(X, A, Y_), M), member(Y_ : Alpha, Δ)), []),
    max_distance(M, u, X, Distance),
    (Distance < Depth; \+loop(X, M, Γ, Δ, _)), !,
    gensym(y_, Y).

match__([], _, _).

match__([_ : F | T], Δ, Y) :-
    member(Y : F, Δ),
    match__(T, Δ, Y).

match_([], Δ_F, _, Δ, Y) :-
    match__(Δ_F, Δ, Y).

match_([_ : F | T], Δ_F, Γ, Δ, Y) :-
    member(Y : F, Γ),
    match_(T, Δ_F, Γ, Δ, Y).

match([], [X : F | T], _, Δ, Y) :-
    member(Y : F, Δ),
    X \= Y,
    match__(T, Δ, Y).

match([X : F | T], Δ_F, Γ, Δ, Y) :-
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

t(X, M, Γ, X : A says Phi) :-
    !, ancestors_says(M, X, Y),
    member(Y : A says Phi, Γ).

t(X, M, Γ, X : Phi -> Psi) :-
    !, ancestors_imp(M, X, Y),
    member(Y : Phi -> Psi, Γ).

t(X, _, _, X : _).

f(X, X : _).

loop(X, M, Γ, Δ, Y) :-
    include(f(X), Δ, Δ_F),
    include(t(X, M, Γ), Γ, Γ_T),
    match(Γ_T, Δ_F, Γ, Δ, Y).

expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X, Γ),
    l_rules(X, (Σ, M, Γ, Δ), Depth, Used, Used_, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used_, Abducibles_L), prove(R, Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used_, Abducibles)).

expand_l_rules(F, Depth, Used, Abducibles) :-
    frame_rules(F, Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Δ), _, Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], Δ)) :-
    \+memberchk(X : Alpha, Γ);
    \+memberchk(X : Beta, Γ).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [X : Alpha | Γ], Δ), (Σ, M, [X : Beta | Γ], Δ)]) :-
    \+memberchk(X : Alpha, Γ),
    \+memberchk(X : Beta, Γ).

% → L
l_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, [(X <= Y, Alpha -> Beta) | Used], [(Σ, M, [X : Alpha -> Beta, Y : Beta | Γ], Δ), (Σ, M, [X : Alpha -> Beta | Γ], [Y : Alpha | Δ])]) :-
    member(X <= Y, M),
    max_distance(M, u, Y, Distance),
    Distance =< Depth,
    \+memberchk((X <= Y, Alpha -> Beta), Used),
    (\+memberchk(Y : Beta, Γ); \+memberchk(Y : Alpha, Δ)).

% says L
l_rules(X : A says Alpha, (Σ, M, Γ, Δ), _, Used, [(s(X, A, Y), A says Alpha) | Used], (Σ, M, [X : A says Alpha, Y : Alpha | Γ], Δ)) :-
    member(s(X, A, Y), M),
    \+memberchk(Y : Alpha, Γ),
    \+memberchk((s(X, A, Y), A says Alpha), Used).

% refl
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X, Σ),
    \+memberchk(X <= X, M), !,
    prove((Σ, [X <= X | M], Γ, Δ), Depth, Used, Abducibles).

% trans
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !,
    prove((Σ, [X <= Z | M], Γ, Δ), Depth, Used, Abducibles).

% mon-S
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    prove((Σ, [s(X, A, Z) | M], Γ, Δ), Depth, Used, Abducibles).

% I
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    prove((Σ, [s(X, A, Z) | M], Γ, Δ), Depth, Used, Abducibles).

% basic-sf
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(X, B, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(s(X, A, Y), M), !,
    prove((Σ, [s(X, A, Y) | M], Γ, Δ), Depth, Used, Abducibles).

% refl-sf
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    append(Γ, Δ, ΓΔ), set_principals(ΓΔ, P),
    member(A, P),
    member(X, Σ),
    \+memberchk(X : A sf A, Γ), !,
    prove((Σ, M, [X : A sf A | Γ], Δ), Depth, Used, Abducibles).

% trans-sf
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X : A sf B, Γ),
    member(X : B sf C, Γ),
    \+memberchk(X : A sf C, Γ), !,
    prove((Σ, M, [X : A sf C | Γ], Δ), Depth, Used, Abducibles).

% mon1-sf
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    prove((Σ, M, [Y : A sf B | Γ], Δ), Depth, Used, Abducibles).

% mon2-sf
frame_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    prove((Σ, M, [Y : A sf B | Γ], Δ), Depth, Used, Abducibles).

frame_rules(F, Depth, Used, Abducibles) :-
    cm(F, Depth, Used, Abducibles).

% CM
cm(F, _, _, F).
