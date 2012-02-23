get_x_in_hp([], _, []).

get_x_in_hp([Y : P | T], M, [XPs | X_in_hp_T]) :-
    atom(P),
    findall(X : P, member(Y <= X, M), XPs), !,
    get_x_in_hp(T, M, X_in_hp_T).

get_x_in_hp([_ | T], M, X_in_hp_T) :-
    get_x_in_hp(T, M, X_in_hp_T).

% mon-S
sat_rules((Σ, M), (Σ, [s(X, A, W) | M])) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    member(Z <= W, M),
    \+memberchk(s(X, A, W), M), !.

% trans
sat_rules((Σ, M), (Σ, [X <= Z | M])) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M), !.

% refl
sat_rules((Σ, M), (Σ, [X <= X | M])) :-
    member(X, Σ),
    \+memberchk(X <= X, M), !.

% s-I-SS
sat_rules((Σ, M), (Σ, [s(X, A, Z) | M])) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M), !.

% s-C
sat_rules((Σ, M), (Σ, [s(Y, A, Y) | M])) :-
    member(s(_, A, Y), M),
    \+memberchk(s(Y, A, Y), M), !.

% CM
sat_rules((Σ, M), (Σ, M)).

saturate((Σ, M10b12b), M10b12b_S) :-
    sat_rules((Σ, M10b12b), (Σ, M10b12b_)),
    ((M10b12b = M10b12b_) ->
        M10b12b_S = M10b12b_;
        saturate((Σ, M10b12b_), M10b12b_S)).

loop_(X, M, Γ, Γ_S, Δ, Δ_S, Y) :-
    append(Γ, Γ_S, Γ_), append(Δ, Δ_S, Δ_),
    loop(X, M, Γ_, Δ_, Y).

ancestors(M, X, Y) :-
    select(Y <= X, M, _); select(s(Y, _, X), M, _).

ancestors(M, X, Y) :-
    (select(W <= X, M, M_); select(s(W, _, X), M, M_)),
    ancestors(M_, W, Y).

m2m10b12b((M10b12b, _, _, [], _), M10b12b) :- !.

m2m10b12b((M, Γ, Γ_S, [X : A says Alpha | T], Δ_S), M10b12b) :-
    ancestors(M, X, Y), X \= Y, loop_(X, M, Γ, Γ_S, [X : A says Alpha | T], Δ_S, Y), !,
    m2m10b12b(([X <= Y | M], Γ, Γ_S, T, Δ_S), M10b12b).

m2m10b12b((M, Γ, Γ_S, [X : Alpha -> Beta  | T], Δ_S), M10b12b) :-
    ancestors(M, X, Y), X \= Y, loop_(X, M, Γ, Γ_S, [X : Alpha -> Beta | T], Δ_S, Y), !,
    m2m10b12b(([X <= Y | M], Γ, Γ_S, T, Δ_S), M10b12b).

m2m10b12b((M, Γ, Γ_S, [_ | T], Δ_S), M10b12b) :-
    m2m10b12b((M, Γ, Γ_S, T, Δ_S), M10b12b).

countermodels((Σ, M, Γ, Γ_S, Δ, Δ_S), (Σ, M10b12b_S, X_in_hp)) :-
    m2m10b12b((M, Γ, Γ_S, Δ, Δ_S), M10b12b),
    saturate((Σ, M10b12b), M10b12b_S),
    get_x_in_hp(Γ, M, X_in_hpFS), flatten(X_in_hpFS, X_in_hpS), list_to_set(X_in_hpS, X_in_hp).
