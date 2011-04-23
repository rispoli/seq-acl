print_graph([], _) :- !.

print_graph([H | T], Labels) :-
    (
        (
            H =.. [<=, X, Y],
            memberchk(X, Labels),
            memberchk(Y, Labels),
            X \= Y,
            format('\t~w -> ~w;~n', [X, Y])
        );
        (
            H =.. [F_, X, A, Y],
            memberchk(X, Labels),
            memberchk(Y, Labels),
            functor2string(F_, F),
            format('\t~w -> ~w [ label = " ", texlbl = "$~w_~w$" ];~n', [X, Y, F, A])
        )
    ), !,
    print_graph(T, Labels).

print_graph([_ | T], Labels) :-
    print_graph(T, Labels).

get_label(X : _, X).

format_label_neg_formula(F_) :-
    proposition2string(_, F_, F),
    format('\\sim ~w\\\\ ', F).

format_label_formula(F_) :-
    proposition2string(_, F_, F),
    format('~w\\\\ ', F).

check_label(X, X : _).

print_worlds([], []).

print_worlds([X : F | T], Δ) :-
    partition(check_label(X), T, Xs, NotXs),
    partition(check_label(X), Δ, Xs_Δ, NotXs_Δ),
    format('\t~w [ texlbl = "$\\begin{matrix}', X),
    maplist(format_label_formula, [X : F | Xs]),
    maplist(format_label_neg_formula, Xs_Δ),
    format('\\end{matrix}$" ];~n'),
    print_worlds(NotXs, NotXs_Δ).

print_worlds([], Δ) :-
    partition(check_label(X), Δ, Xs_Δ, NotXs_Δ),
    format('\t~w [ texlbl = "$\\begin{matrix}', X),
    maplist(format_label_neg_formula, Xs_Δ),
    format('\\end{matrix}$" ];~n'),
    print_worlds([], NotXs_Δ).

m2dot(M, Γ, Δ, Filename) :-
    tell(Filename),
    format('digraph G {~n\tu [ texlbl = "$u$" ];~n'),
    print_worlds(Γ, Δ),
    maplist(get_label, Γ, Labels_Γ),
    maplist(get_label, Δ, Labels_Δ),
    union(Labels_Γ, Labels_Δ, Labels),
    print_graph(M, [u | Labels]),
    format('}'),
    told.
