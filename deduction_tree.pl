:- [inference_rules_axioms].
:- [depth_distance].
:- dynamic(non_provable/0).

expand_premises([], _, _, _, []).

expand_premises([H | T], Depth, Principals, Used, [T1 | T2]) :-
    search_nodes(H, Depth, Principals, Used, T1),
    expand_premises(T, Depth, Principals, Used, T2).

expand_la(F, Depth, Principals, Used, ([F, Premises], Rule)) :-
    inference_rule_la(F, Depth, Principals, Used, Premises, Rule), !.

expand_la(F, _, _, _, ([F, []], '')) :-
    assert(non_provable), !.

expand(F, Depth, Principals, Used, ([F, Premises_tree], Rule)) :-
    inference_rule(F, Depth, Principals, Used, Used_, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Used_, Premises_tree).

expand(F, Depth, Principals, Used, T) :-
    expand_la(F, Depth, Principals, Used, T).

expand_l((Σ, M, Γ, Δ), Depth, Principals, Used, ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    member(X, Γ),
    inference_rule_l(X, (Σ, M, Γ, Δ), Used, Used_, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Used_, Premises_tree).

expand_l(F, Depth, Principals, Used, T) :-
    expand(F, Depth, Principals, Used, T).

expand_r((Σ, M, Γ, Δ), Depth, Principals, Used, ([(Σ, M, Γ, Δ), Premises_tree], Rule)) :-
    inference_rule_r(Δ, (Σ, M, Γ, Δ), Depth, Principals, Used, Premises, Rule), !,
    ((Rule = '\\lor\\mbox{R}') ->
        Premises_tree = Premises;
        expand_premises(Premises, Depth, Principals, Used, Premises_tree)).

expand_r(F, Depth, Principals, Used, T) :-
    expand_l(F, Depth, Principals, Used, T).

expand_sem(F, Depth, Principals, Used, ([F, Premises_tree], Rule)) :-
    inference_rule_sem(F, Premises, Rule), !,
    expand_premises(Premises, Depth, Principals, Used, Premises_tree).

expand_sem(F, Depth, Principals, Used, T) :-
    expand_r(F, Depth, Principals, Used, T).

search_nodes((Σ, M, Γ, Δ), _, _, _, ([(Σ, M, Γ, Δ), []], Rule)) :-
    axiom(M, Γ, Δ, Rule), !.

search_nodes(F, Depth, Principals, Used, T) :-
    expand_sem(F, Depth, Principals, Used, T).

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
    ((Fn = says) ->
        ([A, As] = Args,
        principals(As, Ps),
        P = [A | Ps]);
        foldr(principals, [], Args, P)).

prove(F, T) :-
    depth(F, D),
    principals(F, P_l), list_to_set(P_l, P),
    retractall(non_provable), reset_gensym,
    search_nodes(([u], [], [], u : F), D, P, [], T).

prove(F) :-
    prove(F, _), \+non_provable.
