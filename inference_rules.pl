:- [principals].

:- op(400, xfy, sf),
   op(450, xfy, says),
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

in___((Σ1, M1, Γ1, Γ1_S, Δ1, Δ_S1), (Σ2, M2, Γ2, Γ2_S, Δ2, Δ_S2), (Σ, M, Γ, Γ_S, Δ, Δ_S)) :-
    union(Σ1, Σ2, Σ),
    union(M1, M2, M),
    union(Γ1, Γ2, Γ),
    union(Γ1_S, Γ2_S, Γ_S),
    (is_list(Δ2) -> Δ = [Δ1 | Δ2]; Δ = [Δ1, Δ2]),
    union(Δ_S1, Δ_S2, Δ_S).

un(empty, empty, empty) :- !.

un(empty, H, [H]) :- !.

un(H, empty, [H]) :- !.

un(H1, H2, [H1, H2]).

% ⊤ R
prove((_, _, _, _, _ : top, _), Current_Depth, Max_Depth, _, empty) :-
    Current_Depth =< Max_Depth, !.

% init
prove((_, M, Γ, _, Y : P, _), Current_Depth, Max_Depth, _, empty) :-
    Current_Depth =< Max_Depth,
    member(X <= Y, M),
    member(X : P, Γ), !.

% ⊥ L
prove((_, _, Γ, _, _, _), Current_Depth, Max_Depth, _, empty) :-
    Current_Depth =< Max_Depth,
    memberchk(_ : bot, Γ).

prove((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    r_rules(Δ, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

% ∧ R
r_rules(X : Alpha and Beta, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    Current_Depth_ is Current_Depth + 1,
    !, prove((Σ, M, Γ, Γ_S, X : Alpha, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles_Alpha),
    prove((Σ, M, Γ, Γ_S, X : Beta, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles_Beta),
    un(Abducibles_Alpha, Abducibles_Beta, Abducibles).

% ∨ R
r_rules(X : Alpha or Beta, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    Current_Depth_ is Current_Depth + 1,
    !, prove((Σ, M, Γ, Γ_S, X : Alpha, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles_Alpha),
    ((Abducibles_Alpha = empty) ->
        Abducibles = empty;
        (prove((Σ, M, Γ, Γ_S, X : Beta, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles_Beta),
        ((Abducibles_Beta = empty) ->
            Abducibles = empty;
            in(Abducibles_Alpha, Abducibles_Beta, Abducibles)))).

% → R
r_rules(X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    (Current_Depth =< Max_Depth; (append(Γ, Γ_S, Γ_), \+loop(X, M, Γ_, [X : Alpha -> Beta | Δ_S]))), !,
    gensym(y_, Y),
    Current_Depth_ is Current_Depth + 1,
    prove(([Y | Σ], [X <= Y | M], [Y : Alpha | Γ], Γ_S, Y : Beta, [X : Alpha -> Beta | Δ_S]), Current_Depth_, Max_Depth, Used, Abducibles).

% says R
r_rules(X : A says Alpha, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    (Current_Depth =< Max_Depth; (append(Γ, Γ_S, Γ_), \+loop(X, M, Γ_, [X : A says Alpha | Δ_S]))), !,
    gensym(y_, Y),
    Current_Depth_ is Current_Depth + 1,
    prove(([Y | Σ], [s(X, A, Y) | M], Γ, Γ_S, Y : Alpha, [X : A says Alpha | Δ_S]), Current_Depth_, Max_Depth, Used, Abducibles).

r_rules(Δ, (Σ, M, Γ, Γ_S, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    expand_l_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

match__([], _, _).

match__([_ : F | T], Δ, Y) :-
    member(Y : F, Δ),
    match__(T, Δ, Y).

match_([], Δ_F, _, Δ, Y) :-
    match__(Δ_F, Δ, Y).

match_([_ : F | T], Δ_F, Γ, Δ, Y) :-
    member(Y : F, Γ),
    match_(T, Δ_F, Γ, Δ, Y).

match([], [X : F | T], _, Δ) :-
    member(Y : F, Δ),
    X \= Y,
    match__(T, Δ, Y).

match([X : F | T], Δ_F, Γ, Δ) :-
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

loop(X, M, Γ, Δ) :-
    include(f(X), Δ, Δ_F),
    include(t(X, M, Γ), Γ, Γ_T),
    match(Γ_T, Δ_F, Γ, Δ).

expand_l_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    select(X, Γ, Γ_X),
    l_rules(X, (Σ, M, Γ_X, Γ_S, Δ, Δ_S), Used, Used_, Result), !,
    Current_Depth_ is Current_Depth + 1,
    (is_list(Result) ->
        ([L, R] = Result, prove(L, Current_Depth_, Max_Depth, Used_, Abducibles_L), prove(R, Current_Depth_, Max_Depth, Used_, Abducibles_R), un(Abducibles_L, Abducibles_R, Abducibles));
        prove(Result, Current_Depth_, Max_Depth, Used_, Abducibles)).

expand_l_rules(F, Current_Depth, Max_Depth, Used, Abducibles) :-
    sem_rules(F, Current_Depth, Max_Depth, Used, Abducibles).

% ∧ L
l_rules(X : Alpha and Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Used, Used, (Σ, M, [X : Alpha, X : Beta | Γ], [X : Alpha and Beta | Γ_S], Δ, Δ_S)).

% ∨ L
l_rules(X : Alpha or Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Used, Used, [(Σ, M, [X : Alpha | Γ], [X : Alpha or Beta | Γ_S], Δ, Δ_S), (Σ, M, [X : Beta | Γ], [X : Alpha or Beta | Γ_S], Δ, Δ_S)]).

% says L
l_rules(X : A says Alpha, (Σ, M, Γ, Γ_S, Δ, Δ_S), Used, [(s(X, A, Y), A says Alpha) | Used], (Σ, M, [X : A says Alpha, Y : Alpha | Γ], Γ_S, Δ, Δ_S)) :-
    member(s(X, A, Y), M),
    \+memberchk((s(X, A, Y), A says Alpha), Used).

% mon-S
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [s(X, A, W) | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% trans
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [X <= Z | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% refl
sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X, Σ),
    \+memberchk(X <= X, M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [X <= X | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

sem_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

% s-I-SS
ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [s(X, A, Z) | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% unit
%ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
%    Current_Depth =< Max_Depth,
%    member(s(X, _, Y), M),
%    \+memberchk(X <= Y, M), !,
%    Current_Depth_ is Current_Depth + 1,
%    prove((Σ, [X <= Y | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% s-C
ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [s(Y, A, Y) | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    left_arrow((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles), !.

ac_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

la(_ : _ -> _).

% → L
left_arrow((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    include(la, Γ, Γ_la),
    ((Γ_la = []) ->
        fail;
        (la_f(Γ_la, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles), ((Abducibles = eol) -> fail; true))).

lal(X, X <= _).

la_f([], _, _, _, _, eol).

la_f([X : Alpha -> Beta | T], (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    include(lal(X), M, M_lal),
    ((M_lal = []) ->
        fail;
        (la_l(M_lal, X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles_H), !,
        ((Abducibles_H = empty) ->
            Abducibles = empty;
            (la_f(T, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles_T), in(Abducibles_H, Abducibles_T, Abducibles))))).

la_f([_ | T], (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    la_f(T, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

la_l([], _, _, _, _, _, eol).

la_l([X <= Y | T], X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    \+memberchk(Y : Beta, Γ),
    \+memberchk((X <= Y, Alpha -> Beta), Used), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, M, [Y : Beta | Γ], Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, [(X <= Y, Alpha -> Beta) | Used], Abducibles_Beta),
    ((Abducibles_Beta = empty) ->
        (prove((Σ, M, Γ, Γ_S, Y : Alpha, Δ_S), Current_Depth_, Max_Depth, [(X <= Y, Alpha -> Beta) | Used], Abducibles_Alpha),
        ((Abducibles_Alpha = empty) ->
            Abducibles = empty;
            (la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles_T), in(Abducibles_Alpha, Abducibles_T, Abducibles))));
            la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles)).

la_l([_ | T], X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    la_l(T, X : Alpha -> Beta, (Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

% sf-refl
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X, Σ),
    append(Γ, [Δ], ΓΔ), set_principals(ΓΔ, P),
    member(A, P),
    \+memberchk(X : A sf A, Γ), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, M, [X : A sf A | Γ], Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% sf
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(s(X, B, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(s(X, A, Y), M), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, [s(X, A, Y) | M], Γ, Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% sf-trans
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X : A sf B, Γ),
    member(X : B sf C, Γ),
    \+memberchk(X : A sf C, Γ), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, M, [X : A sf C | Γ], Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% sf-unit
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(s(X, _, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, M, [Y : A sf B | Γ], Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

% sf-mon
sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    Current_Depth =< Max_Depth,
    member(X <= Y, M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ), !,
    Current_Depth_ is Current_Depth + 1,
    prove((Σ, M, [Y : A sf B | Γ], Γ_S, Δ, Δ_S), Current_Depth_, Max_Depth, Used, Abducibles).

sf_rules((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles) :-
    cm((Σ, M, Γ, Γ_S, Δ, Δ_S), Current_Depth, Max_Depth, Used, Abducibles).

% CM
cm((Σ, M, Γ, Γ_S, Δ, Δ_S), _, _, _, (Σ, M, Γ, Γ_S, Δ, Δ_S)).
