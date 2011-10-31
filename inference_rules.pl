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
    (Distance < Depth; (append(Γ, Γ_S, Γ_), append(Δ, Δ_S, Δ_), \+loop(X, M, Γ_, [X : Alpha -> Beta | Δ_]))), !,
    gensym(y_, Y).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, ([Y | Σ], [s(X, A, Y) | M], Γ, Γ_S, [Y : Alpha | Δ], [X : A says Alpha | Δ_S])) :-
    max_distance(M, u, X, Distance),
    (Distance < Depth; (append(Γ, Γ_S, Γ_), append(Δ, Δ_S, Δ_), \+loop(X, M, Γ_, [X : A says Alpha | Δ_]))), !,
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

match__([_ : F | T], Δ, Y) :-
    member(Y : F, Δ),
    match__(T, Δ, Y).

match_([], Δ_X, _, Δ, Y) :-
    match__(Δ_X, Δ, Y).

match_([_ : F | T], Δ_X, Γ, Δ, Y) :-
    member(Y : F, Γ),
    match_(T, Δ_X, Γ, Δ, Y).

match([], [_ : F | T], A, _, Δ) :-
    member(Y : F, Δ),
    member(Y, A),
    match__(T, Δ, Y).

match([_ : F | T], Δ_X, A, Γ, Δ) :-
    member(Y : F, Γ),
    member(Y, A),
    match_(T, Δ_X, Γ, Δ, Y).

loop(X, M, Γ, Δ) :-
    ancestors(M, X, A),
    include(label_X(X), Δ, Δ_X),
    include(label_X(X), Γ, Γ_X),
    match(Γ_X, Δ_X, A, Γ, Δ).

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
    cm((Σ, M, Γ, Γ_S, Δ, Δ_S), Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Γ_S, Δ, Δ_S), _, _, (Σ, M, Γ, Γ_S, Δ, Δ_S)).
