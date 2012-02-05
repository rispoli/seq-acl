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
prove((_, _, _, _, Δ, _), _, _, empty) :-
    memberchk(_ : top, Δ), !.

% init
prove((_, M, Γ, _, Δ, _), _, _, empty) :-
    member(Y : P, Δ),
    member(X <= Y, M),
    member(X : P, Γ), !.

% ⊥ L
prove((_, _, Γ, _, _, _), _, _, empty) :-
    memberchk(_ : bot, Γ).

prove((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    expand_r_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

expand_r_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    select(X, Δ, Δ_X),
    r_rules(X, (Σ, M, Γ, Γ_S, Δ_X, Δ_S), Depth, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used, Abducibles_L), prove(R, Depth, Used, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used, Abducibles)).

expand_r_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    expand_l_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), _, [(Σ, M, Γ, Γ_S, [X : Alpha | Δ], Δ_S), (Σ, M, Γ, Γ_S, [X : Beta | Δ], Δ_S)]).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), _, (Σ, M, Γ, Γ_S, [X : Alpha, X : Beta | Δ], Δ_S)).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, ([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], Γ_S, [Y : Beta | Δ], [X : Alpha -> Beta | Δ_S])) :-
    max_distance(M, u, X, Distance),
    (Distance < Depth; (append(Γ, Γ_S, Γ_), append(Δ, Δ_S, Δ_), \+loop(X, M, Γ_, [X : Alpha -> Beta | Δ_], _))), !,
    gensym(y_, Y).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, ([Y | Σ], [s(X, A, Y) | M], Γ, Γ_S, [Y : Alpha | Δ], [X : A says Alpha | Δ_S])) :-
    max_distance(M, u, X, Distance),
    (Distance < Depth; (append(Γ, Γ_S, Γ_), append(Δ, Δ_S, Δ_), \+loop(X, M, Γ_, [X : A says Alpha | Δ_], _))), !,
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

expand_l_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    select(X, Γ, Γ_X),
    l_rules(X, (Σ, M, Γ_X, Γ_S, Δ, Δ_S), Depth, Used, Used_, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used_, Abducibles_L), prove(R, Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used_, Abducibles)).

expand_l_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), _, Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], [X : Alpha and Beta | Γ_S], Δ, Δ_S)).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), _, Used, Used, [(Σ, M, [X : Alpha | Γ], [X : Alpha or Beta | Γ_S], Δ, Δ_S), (Σ, M, [X : Beta | Γ], [X : Alpha or Beta | Γ_S], Δ, Δ_S)]).

% → L
l_rules(X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, [(X <= Y, Alpha -> Beta) | Used], [(Σ, M, [X : Alpha -> Beta, Y : Beta | Γ], Γ_S, Δ, Δ_S), (Σ, M, [X : Alpha -> Beta | Γ], Γ_S, [Y : Alpha | Δ], Δ_S)]) :-
    member(X <= Y, M),
    max_distance(M, u, Y, Distance),
    Distance =< Depth,
    \+memberchk((X <= Y, Alpha -> Beta), Used),
    (\+memberchk(Y : Beta, Γ); \+memberchk(Y : Alpha, Δ)).

% says L
l_rules(X : A says Alpha, (Σ, M, Γ, Γ_S, Δ, Δ_S), _, Used, [(s(X, A, Y), A says Alpha) | Used], (Σ, M, [X : A says Alpha, Y : Alpha | Γ], Γ_S, Δ, Δ_S)) :-
    member(s(X, A, Y), M),
    \+memberchk((s(X, A, Y), A says Alpha), Used).

% mon-S
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M), !,
    prove((Σ, [s(X, A, W) | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% trans
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !,
    prove((Σ, [X <= Z | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% refl
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X, Σ),
    \+memberchk(X <= X, M), !,
    prove((Σ, [X <= X | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% s-I-SS
ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    prove((Σ, [s(X, A, Z) | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% unit
%ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
%    member(s(X, _, Y), M),
%    \+memberchk(X <= Y, M), !,
%    prove((Σ, [X <= Y | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% s-C
ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !,
    prove((Σ, [s(Y, A, Y) | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% sf-refl
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X, Σ),
    append([Γ, Γ_S, Δ, Δ_S], ΓΔ), set_principals(ΓΔ, P),
    member(A, P),
    \+memberchk(X : A sf A, Γ), !,
    prove((Σ, M, [X : A sf A | Γ], Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% sf
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(X, B, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(s(X, A, Y), M), !,
    prove((Σ, [s(X, A, Y) | M], Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% sf-trans
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X : A sf B, Γ),
    member(X : B sf C, Γ),
    \+memberchk(X : A sf C, Γ), !,
    prove((Σ, M, [X : A sf C | Γ], Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% sf-unit
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    prove((Σ, M, [Y : A sf B | Γ], Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% sf-mon
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    prove((Σ, M, [Y : A sf B | Γ], Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles) :-
    cm((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Γ_S, Δ, Δ_S), _, _, (Σ, M, Γ, Γ_S, Δ, Δ_S)).
