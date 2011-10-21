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
prove((_, _, _, Δ, _), _, _, empty) :-
    memberchk(_ : top, Δ), !.

% init
prove((_, M, Γ, Δ, _), _, _, empty) :-
    member(Y : P, Δ),
    member(X <= Y, M),
    member(X : P, Γ), !.

% ⊥ L
prove((_, _, Γ, _, _), _, _, empty) :-
    memberchk(_ : bot, Γ).

prove((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    expand_r_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles).

expand_r_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    select(X, Δ, Δ_X),
    r_rules(X, (Σ, M, Γ, Δ_X, Δ_S), Depth, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used, Abducibles_L), prove(R, Depth, Used, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used, Abducibles)).

expand_r_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    expand_l_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ, Δ, Δ_S), _, [(Σ, M, Γ, [X : Alpha | Δ], Δ_S), (Σ, M, Γ, [X : Beta | Δ], Δ_S)]).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ, Δ, Δ_S), _, (Σ, M, Γ, [X : Alpha, X : Beta | Δ], Δ_S)).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ, Δ_S), Depth, ([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], [Y : Beta | Δ], [X : Alpha -> Beta | Δ_S])) :-
    max_distance(M, u, X, Distance),
    (Distance < Depth; \+loop(X, M, Γ, [X : Alpha -> Beta | Δ_S])), !,
    gensym(y_, Y).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Δ, Δ_S), Depth, ([Y | Σ], [s(X, A, Y) | M], Γ, [Y : Alpha | Δ], [X : A says Alpha | Δ_S])) :-
    max_distance(M, u, X, Distance),
    (Distance < Depth; \+loop(X, M, Γ, [X : A says Alpha | Δ_S])), !,
    gensym(y_, Y).

ancestors_([], _, _, []).

ancestors_([W <= X | T], M, X, A) :-
    !, ancestors_(T, M, X, AT),
    ancestors_(M, M, W, AW),
    append([W | AT], AW, A).

ancestors_([s(W, _, X) | T], M, X, A) :-
    !, ancestors_(T, M, X, AT),
    ancestors_(M, M, W, AW),
    append([W | AT], AW, A).

ancestors_([_ | T], M, X, AT) :-
    ancestors_(T, M, X, AT).

ancestors(M, X, A) :-
    ancestors_(M, M, X, A_L),
    list_to_set(A_L, A_S),
    subtract(A_S, [X], A).

label_X(X, X : _).

match__([], _, _).

match__([_ : F | T], Δ_S, Y) :-
    member(Y : F, Δ_S),
    match__(T, Δ_S, Y).

match_([], Δ_S_X, _, Δ_S, Y) :-
    match__(Δ_S_X, Δ_S, Y).

match_([_ : F | T], Δ_S_X, Γ, Δ_S, Y) :-
    member(Y : F, Γ),
    match_(T, Δ_S_X, Γ, Δ_S, Y).

match([], [_ : F | T], A, _, Δ_S) :-
    member(Y : F, Δ_S),
    member(Y, A),
    match__(T, Δ_S, Y).

match([_ : F | T], Δ_S_X, A, Γ, Δ_S) :-
    member(Y : F, Γ),
    member(Y, A),
    match_(T, Δ_S_X, Γ, Δ_S, Y).

loop(X, M, Γ, Δ_S) :-
    ancestors(M, X, A),
    include(label_X(X), Δ_S, Δ_S_X),
    include(label_X(X), Γ, Γ_X),
    match(Γ_X, Δ_S_X, A, Γ, Δ_S).

expand_l_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    select(X, Γ, Γ_X),
    l_rules(X, (Σ, M, Γ_X, Δ, Δ_S), Depth, Used, Used_, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used_, Abducibles_L), prove(R, Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used_, Abducibles)).

expand_l_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    sem_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Δ, Δ_S), _, Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], Δ, Δ_S)).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Δ, Δ_S), _, Used, Used, [(Σ, M, [X : Alpha | Γ], Δ, Δ_S), (Σ, M, [X : Beta | Γ], Δ, Δ_S)]).

% → L
l_rules(X : Alpha -> Beta, (Σ, M, Γ, Δ, Δ_S), Depth, Used, [(X <= Y, Alpha -> Beta) | Used], [(Σ, M, [X : Alpha -> Beta, Y : Beta | Γ], Δ, Δ_S), (Σ, M, [X : Alpha -> Beta | Γ], [Y : Alpha | Δ], Δ_S)]) :-
    member(X <= Y, M),
    max_distance(M, u, Y, Distance),
    Distance =< Depth,
    \+memberchk((X <= Y, Alpha -> Beta), Used),
    (\+memberchk(Y : Beta, Γ); \+memberchk(Y : Alpha, Δ)).

% says L
l_rules(X : A says Alpha, (Σ, M, Γ, Δ, Δ_S), _, Used, [(s(X, A, Y), A says Alpha) | Used], (Σ, M, [X : A says Alpha, Y : Alpha | Γ], Δ, Δ_S)) :-
    member(s(X, A, Y), M),
    \+memberchk((s(X, A, Y), A says Alpha), Used).

% mon-S
sem_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M), !,
    prove((Σ, [s(X, A, W) | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

% trans
sem_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !,
    prove((Σ, [X <= Z | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

% refl
sem_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(X, Σ),
    \+memberchk(X <= X, M), !,
    prove((Σ, [X <= X | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

sem_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    ac_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles).

% s-I-SS
ac_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    prove((Σ, [s(X, A, Z) | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

% unit
%ac_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
%    member(s(X, _, Y), M),
%    \+memberchk(X <= Y, M), !,
%    prove((Σ, [X <= Y | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

% s-C
ac_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !,
    prove((Σ, [s(Y, A, Y) | M], Γ, Δ, Δ_S), Depth, Used, Abducibles).

ac_rules((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles) :-
    cm((Σ, M, Γ, Δ, Δ_S), Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Δ, Δ_S), _, _, (Σ, M, Γ, Δ, Δ_S)).
