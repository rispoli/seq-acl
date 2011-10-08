:- op(450, xfy, says),
   op(500, yfx, and),
   op(600, yfx, or),
   op(700, xfy, ->),
   op(800, xfx, :),
   op(700, xfx, <=).

in(H, eol, H) :- !.

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

in___(empty, _, empty).

in___(_, empty, empty).

in___((Σ1, M1, Γ1, Δ1), (Σ2, M2, Γ2, Δ2), (Σ, M, Γ, [Δ1, Δ2])) :-
    union(Σ1, Σ2, Σ),
    union(M1, M2, M),
    union(Γ1, Γ2, Γ).

un(empty, empty, empty) :- !.

un(empty, H, [H]) :- !.

un(H, empty, [H]) :- !.

un(H1, H2, [H1, H2]).

% ⊤ R
prove((_, _, _, _ : top), _, _, empty) :- !.

% init
prove((_, M, Γ, Y : P), _, _, empty) :-
    member(X <= Y, M),
    member(X : P, Γ), !.

% ⊥ L
prove((_, _, Γ, _), _, _, empty) :-
    memberchk(_ : bot, Γ).

prove((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    r_rules(Δ, (Σ, M, Γ), Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ), Depth, Used, Abducibles) :-
    !, prove((Σ, M, Γ, X : Alpha), Depth, Used, Abducibles_Alpha),
    prove((Σ, M, Γ, X : Beta), Depth, Used, Abducibles_Beta),
    un(Abducibles_Alpha, Abducibles_Beta, Abducibles).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ), Depth, Used, Abducibles) :-
    !, prove((Σ, M, Γ, X : Alpha), Depth, Used, Abducibles_Alpha),
    ((Abducibles_Alpha = empty) ->
        Abducibles = empty;
        (prove((Σ, M, Γ, X : Beta), Depth, Used, Abducibles_Beta),
        ((Abducibles_Beta = empty) ->
            Abducibles = empty;
            in(Abducibles_Alpha, Abducibles_Beta, Abducibles)))).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ), Depth, Used, Abducibles) :-
    max_distance(M, u, X, Distance),
    Distance =< Depth, !,
    gensym(y_, Y),
    prove(([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], Y : Beta), Depth, Used, Abducibles).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ), Depth, Used, Abducibles) :-
    max_distance(M, u, X, Distance),
    Distance =< Depth, !,
    gensym(y_, Y),
    prove(([Y | Σ], [s(X, A, Y) | M], Γ, Y : Alpha), Depth, Used, Abducibles).

r_rules(Δ, (Σ, M, Γ), Depth, Used, Abducibles) :-
    expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    select(X, Γ, Γ_X),
    l_rules(X, (Σ, M, Γ_X, Δ), Used, Used_, Result), !,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Depth, Used_, Abducibles_L), prove(R, Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Depth, Used_, Abducibles)).

expand_l_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    sem_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Δ), Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], Δ)).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Δ), Used, Used, [(Σ, M, [X : Alpha | Γ], Δ), (Σ, M, [X : Beta | Γ], Δ)]).

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
ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    prove((Σ, [s(X, A, Z) | M], Γ, Δ), Depth, Used, Abducibles).

% s-C
ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !,
    prove((Σ, [s(Y, A, Y) | M], Γ, Δ), Depth, Used, Abducibles).

ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    left_arrow((Σ, M, Γ, Δ), Depth, Used, Abducibles), !.

ac_rules((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    cm((Σ, M, Γ, Δ), Depth, Used, Abducibles).

la(_ : _ -> _).

% → L
left_arrow((Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    include(la, Γ, Γ_la),
    ((Γ_la = []) ->
        fail;
        (la_f(Γ_la, (Σ, M, Γ, Δ), Depth, Used, Abducibles), ((Abducibles = eol) -> fail; true))).

lal(X, X <= _).

la_f([], _, _, _, eol).

la_f([X : Alpha -> Beta | T], (Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    include(lal(X), M, M_lal),
    ((M_lal = []) ->
        fail;
        (la_l(M_lal, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles_H), !,
        ((Abducibles_H = empty) ->
            Abducibles = empty;
            (la_f(T, (Σ, M, Γ, Δ), Depth, Used, Abducibles_T), in(Abducibles_H, Abducibles_T, Abducibles))))).

la_f([_ | T], (Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    la_f(T, (Σ, M, Γ, Δ), Depth, Used, Abducibles).

la_l([], _, _, _, _, eol).

la_l([X <= Y | T], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    \+memberchk(Y : Beta, Γ),
    \+memberchk((X <= Y, Alpha -> Beta), Used), !,
    prove((Σ, M, [Y : Beta | Γ], Δ), Depth, [(X <= Y, Alpha -> Beta) | Used], Abducibles_Beta),
    ((Abducibles_Beta = empty) ->
        (prove((Σ, M, Γ, Y : Alpha), Depth, [(X <= Y, Alpha -> Beta) | Used], Abducibles_Alpha),
        ((Abducibles_Alpha = empty) ->
            Abducibles = empty;
            (la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles_T), in(Abducibles_Alpha, Abducibles_T, Abducibles))));
            la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles)).

la_l([_ | T], X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles) :-
    la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Δ), Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Δ), _, _, (Σ, M, Γ, Δ)).
