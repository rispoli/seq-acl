get_x_in_hp([], _, []).

get_x_in_hp([X : A sf B | T], M, [X : A sf B | X_in_hp_T]) :-
    !, get_x_in_hp(T, M, X_in_hp_T).

get_x_in_hp([Y : P | T], M, [XPs | X_in_hp_T]) :-
    atom(P),
    findall(X : P, member(Y <= X, M), XPs), !,
    get_x_in_hp(T, M, X_in_hp_T).

get_x_in_hp([_ | T], M, X_in_hp_T) :-
    get_x_in_hp(T, M, X_in_hp_T).

% refl
sat_rules((Σ, M, Γ, _), (Σ, [X <= X | M], Γ)) :-
    member(X, Σ),
    \+memberchk(X <= X, M).

% trans
sat_rules((Σ, M, Γ, _), (Σ, [X <= Z | M], Γ)) :-
    member(X <= Y, M),
    member(Y <= Z, M),
    \+memberchk(X <= Z, M).

% mon-S
sat_rules((Σ, M, Γ, _), (Σ, [s(X, A, Z) | M], Γ)) :-
    member(X <= Y, M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M).

% I
sat_rules((Σ, M, Γ, _), (Σ, [s(X, A, Z) | M], Γ)) :-
    member(s(X, _, Y), M),
    member(s(Y, A, Z), M),
    \+memberchk(s(X, A, Z), M).

% basic-sf
sat_rules((Σ, M, Γ, _), (Σ, [s(X, A, Y) | M], Γ)) :-
    member(s(X, B, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(s(X, A, Y), M).

% refl-sf
sat_rules((Σ, M, Γ, Δ), (Σ, M, [X : A sf A | Γ])) :-
    append(Γ, Δ, ΓΔ), set_principals(ΓΔ, P),
    member(A, P),
    member(X, Σ),
    \+memberchk(X : A sf A, Γ).

% trans-sf
sat_rules((Σ, M, Γ, _), (Σ, M, [X : A sf C | Γ])) :-
    member(X : A sf B, Γ),
    member(X : B sf C, Γ),
    \+memberchk(X : A sf C, Γ).

% mon1-sf
sat_rules((Σ, M, Γ, _), (Σ, M, [Y : A sf B | Γ])) :-
    member(X <= Y, M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ).

% mon2-sf
sat_rules((Σ, M, Γ, _), (Σ, M, [Y : A sf B | Γ])) :-
    member(s(X, _, Y), M),
    member(X : A sf B, Γ),
    \+memberchk(Y : A sf B, Γ).

% CM
sat_rules((Σ, M, Γ, _), (Σ, M, Γ)).

saturate((Σ, M10b12b, Γ, Δ), (M10b12b_S, Γ_S)) :-
    sat_rules((Σ, M10b12b, Γ, Δ), (Σ, M10b12b_, Γ_)), !,
    ((M10b12b = M10b12b_, Γ = Γ_) ->
        (M10b12b_S = M10b12b_, Γ_S = Γ_);
        saturate((Σ, M10b12b_, Γ_), (M10b12b_S, Γ_S))).

ancestors(M, X, Y) :-
    select(Y <= X, M, _); select(s(Y, _, X), M, _).

ancestors(M, X, Y) :-
    (select(W <= X, M, M_); select(s(W, _, X), M, M_)),
    ancestors(M_, W, Y).

m2m10b12b((M10b12b, _, []), M10b12b) :- !.

m2m10b12b((M, Γ, [X : A says Alpha | T]), M10b12b) :-
    ancestors(M, X, Y), X \= Y, loop(X, M, Γ, [X : A says Alpha | T], Y), !,
    m2m10b12b(([X <= Y | M], Γ, T), M10b12b).

m2m10b12b((M, Γ, [X : Alpha -> Beta | T]), M10b12b) :-
    ancestors(M, X, Y), X \= Y, loop(X, M, Γ, [X : Alpha -> Beta | T], Y), !,
    m2m10b12b(([X <= Y | M], Γ, T), M10b12b).

m2m10b12b((M, Γ, [_ | T]), M10b12b) :-
    m2m10b12b((M, Γ, T), M10b12b).

countermodels((Σ, M, Γ, Δ), (Σ, M10b12b_S, X_in_hp)) :-
    m2m10b12b((M, Γ, Δ), M10b12b),
    saturate((Σ, M10b12b, Γ, Δ), (M10b12b_S, _)),
    get_x_in_hp(Γ, M, X_in_hpFS), flatten(X_in_hpFS, X_in_hpS), list_to_set(X_in_hpS, X_in_hp).
