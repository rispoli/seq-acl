:- [inference_rules_axioms].

expand_premises([], []).

expand_premises([H | T], [T1 | T2]) :-
    search_nodes(H, T1),
    expand_premises(T, T2).

expand(F, ([F, Premises_tree], Rule)) :-
    inference_rule(F, Premises, Rule), !,
    expand_premises(Premises, Premises_tree).

expand_l((Σ, M, Γ, Δ), ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    select(X, Γ, Γ_minus_X),
    inference_rule_l(X, (Σ, M, Γ_minus_X, Δ), Premises, Rule), !,
    expand_premises(Premises, Premises_tree).

expand_l(F, T) :-
    expand(F, T).

expand_r((Σ, M, Γ, Δ), ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    select(X, Δ, Δ_minus_X),
    inference_rule_r(X, (Σ, M, Γ, Δ_minus_X), Premises, Rule), !,
    expand_premises(Premises, Premises_tree).

expand_r(F, T) :-
    expand_l(F, T).

search_nodes((Σ, M, Γ, Δ), ([(Σ, M, Γ, Δ), []], Rule)) :-
    axiom(M, Γ, Δ, Rule), !.

search_nodes(F, T) :-
    expand_r(F, T).
