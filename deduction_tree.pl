:- [inference_rules_axioms].
:- [depth_distance].

expand_premises([], _, _, []).

expand_premises([H | T], Depth, Principals, [T1 | T2]) :-
    search_nodes(H, Depth, Principals, T1),
    expand_premises(T, Depth, Principals, T2).

expand(F, Depth, Principals, ([F, Premises_tree], Rule)) :-
    inference_rule(F, Depth, Principals, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Premises_tree).

expand_l((Σ, M, Γ, Δ), Depth, Principals, ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    member(X, Γ),
    inference_rule_l(X, (Σ, M, Γ, Δ), Depth, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Premises_tree).

expand_l(F, Depth, Principals, T) :-
    expand(F, Depth, Principals, T).

expand_r((Σ, M, Γ, Δ), Depth, Principals, ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    select(X, Δ, Δ_minus_X),
    inference_rule_r(X, (Σ, M, Γ, Δ_minus_X), Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Premises_tree).

expand_r(F, Depth, Principals, T) :-
    expand_l(F, Depth, Principals, T).

expand_sem(F, Depth, Principals, ([F, Premises_tree], Rule)) :-
    inference_rule_sem(F, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Premises_tree).

expand_sem(F, Depth, Principals, T) :-
    expand_r(F, Depth, Principals, T).

search_nodes((Σ, M, Γ, Δ), _, _, ([(Σ, M, Γ, Δ), []], Rule)) :-
    axiom(M, Γ, Δ, Rule), !.

search_nodes(F, Depth, Principals, T) :-
    expand_sem(F, Depth, Principals, T).

foldr(_, Z, [], Z) :- !.

foldr(F, Z, [X | XS],  O_) :-
    foldr(F, Z, XS, F_O),
    C =.. [F, X, O],
    C,
    append(O, F_O, O_).

principals(A, []) :-
    atom(A), !.

principals(F, P) :-
    F =.. [Fn | Args],
    (member(Fn, [says, c, ratified, p]) ->
        ([A, As] = Args,
        principals(As, Ps),
        P = [A | Ps]);
        foldr(principals, [], Args, P)).

prove(F, T) :-
    depth(F, D),
    principals(F, P_l), list_to_set(P_l, P),
    reset_gensym,
    search_nodes(([u], [], [], [u : F]), D, P, T).

prove(F) :-
    prove(F, _).
