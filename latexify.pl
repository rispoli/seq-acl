:- [deduction_tree].
:- [op_pri].

stringConcat([], Output, Output).

stringConcat([Head|Tail], TempString, Output) :-
    string_concat(TempString, Head, TempString1),
    stringConcat(Tail, TempString1, Output).

join(List, Separator, Output) :-
    inner_join(List, Separator, '', Output), !.

inner_join([], _, _, '').

inner_join([Last], _, TempString, Output) :-
    string_concat(TempString, Last, Output).

inner_join([Head | Tail], Separator, TempString, Output) :-
    stringConcat([Head, Separator], TempString, TempString1),
    inner_join(Tail, Separator, TempString1, Output).

functor2string(and, ' \\land ').
functor2string(or, ' \\lor ').
functor2string(->, ' \\supset ').
functor2string(:, ' : ').
functor2string(<=, ' \\stackrel{\\sim}{\\leq} ').
functor2string(n, 'N').
functor2string(p, 'P').
functor2string([], '\\square').
functor2string(<>, '\\lozenge').

parentheses(Parent_functor, Functor) :-
    op_pri(X, Parent_functor),
    op_pri(Y, Functor), !,
    X \= Y.

proposition2string(_, A, A) :-
    atom(A), !.

proposition2string(_, NorP, String) :-
    NorP =.. [F_, X_, I_, Y_],
    functor2string(F_, F),
    proposition2string(_, X_, X),
    proposition2string(_, I_, I),
    proposition2string(_, Y_, Y),
    stringConcat([X, ' \\stackrel{\\sim}{', F, '_', I, '} ', Y], '', String), !.

proposition2string(_, BoxorDiamond, String) :-
    (F_ = []; F = <>), BoxorDiamond =.. [F_ ,I_, X_],
    functor2string(F_, F),
    proposition2string(_, I_, I),
    proposition2string(_, X_, X),
    (atom(X) ->
        stringConcat([F, '_', I, ' ', X], '', String);
        stringConcat([F, '_', I, ' (', X, ')'], '', String)),
    !.

proposition2string(Parent_functor, B_op, String) :-
    B_op =.. [Functor | Arguments],
    maplist(proposition2string(Functor), Arguments, [A_s, B_s]),
    functor2string(Functor, Functor_s),
    (Parent_functor \= :, parentheses(Parent_functor, Functor) ->
        stringConcat(['(', A_s, Functor_s, B_s, ')'], '', String), !;
        stringConcat([A_s, Functor_s, B_s], '', String)).

print_sequent(Indentation, (Σ, M, Γ_, Δ)) :-
    append([Σ, M, Γ_], Γ),
    maplist(proposition2string(_), Γ, Γ_s),
    maplist(proposition2string(_), Δ, Δ_s),
    join(Γ_s, ', ', Γ_s_j),
    join(Δ_s, ', ', Δ_s_j),
    stringConcat([Indentation, Γ_s_j, ' \\Rightarrow_{\\cal T} ', Δ_s_j, '~n'], '', Sequent_s),
    format(Sequent_s).

print_tree(Indentation, ([Conclusion, Premises], Rule)) :-
    format('~w\\prooftree~n', Indentation),
    string_concat(Indentation, '\t', Deeper_indentation),
    ((Premises \= []) ->
        maplist(print_tree(Deeper_indentation), Premises);
        format('')
    ),
    format('~w\\justifies~n', Indentation),
    print_sequent(Deeper_indentation, Conclusion),
    format('~w\\using~n', Indentation),
    stringConcat(['(', Rule, ')~n'], '', Rule_n),
    format(Deeper_indentation), format(Rule_n),
    format('~w\\endprooftree~n', Indentation).

latexify(Formula, Filename) :-
    reset_gensym,
    search_nodes(Formula, Sequent),
    tell(Filename),
    format('\\documentclass{article}~n\\pagestyle{empty}~n\\usepackage{amsthm, amsmath, amssymb}~n\\usepackage{prooftree}~n\\begin{document}~n~n\\begin{displaymath}~n'),
    print_tree('', Sequent),
    format('\\end{displaymath}~n~n\\end{document}'),
    told.
