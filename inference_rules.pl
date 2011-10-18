:- op(450, xfy, says),
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

prove((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    expand_r_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

expand_r_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    select(X, Δ, Δ_X),
    r_rules(X, (Σ, M, Γ, Δ_X), Depth, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used, Abducibles_L), prove(R, Depth, Used, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used, Abducibles)).

expand_r_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ, Δ), _, [(Σ, M, Γ, [X : Alpha | Δ]), (Σ, M, Γ, [X : Beta | Δ])]).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ, Δ), _, (Σ, M, Γ, [X : Alpha, X : Beta | Δ])).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, ([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ])) :-
    max_distance(M, u, X, Distance),
    Distance =< Depth, !,
    gensym(y_, Y).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Δ), Depth, ([Y | Σ], [s(X, A, Y) | M], Γ, [Y : Alpha | Δ])) :-
    max_distance(M, u, X, Distance),
    Distance =< Depth, !,
    gensym(y_, Y).

expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    select(X, Γ, Γ_X),
    l_rules(X, (Σ, M, Γ_X, Δ), Depth, Used, Used_, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used_, Abducibles_L), prove(R, Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used_, Abducibles)).

expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Δ), _, Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], Δ)).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Δ), _, Used, Used, [(Σ, M, [X : Alpha | Γ], Δ), (Σ, M, [X : Beta | Γ], Δ)]).

% → L
l_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, [(X <= Y, Alpha -> Beta) | Used], [(Σ, M, [X : Alpha -> Beta, Y : Beta | Γ], Δ), (Σ, M, [X : Alpha -> Beta | Γ], [Y : Alpha | Δ])]) :-
    member(X <= Y, M),
    max_distance(M, u, Y, Distance),
    Distance =< Depth,
    \+memberchk((X <= Y, Alpha -> Beta), Used),
    (\+memberchk(Y : Beta, Γ); \+memberchk(Y : Alpha, Δ)).

% says L
l_rules(X : A says Alpha, (Σ, M, Γ, Δ), Used, [(s(X, A, Y), A says Alpha) | Used], (Σ, M, [X : A says Alpha, Y : Alpha | Γ], Δ)) :-
    member(s(X, A, Y), M),
    \+memberchk((s(X, A, Y), A says Alpha), Used).

% mon-S
sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M), !,
    prove((Σ, [s(X, A, W) | M], Γ, Δ), Depth, Used, Abducibles).

% trans
sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !,
    prove((Σ, [X <= Z | M], Γ, Δ), Depth, Used, Abducibles).

% refl
sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(X, Σ),
    \+memberchk(X <= X, M), !,
    prove((Σ, [X <= X | M], Γ, Δ), Depth, Used, Abducibles).

sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

% s-I-SS
%ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
%    member(s(X, _, Y), M),
%    member(s(Y, A, Z), M),
%    \+memberchk(s(X, A, Z), M), !,
%    prove((Σ, [s(X, A, Z) | M], Γ, Δ), Depth, Used, Abducibles).

% unit
ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    \+memberchk(X <= Y, M), !,
    prove((Σ, [X <= Y | M], Γ, Δ), Depth, Used, Abducibles).

% s-C
ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !,
    prove((Σ, [s(Y, A, Y) | M], Γ, Δ), Depth, Used, Abducibles).

ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    cm((Σ, M, Γ, Δ), Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Δ), _, _, (Σ, M, Γ, Δ)).
