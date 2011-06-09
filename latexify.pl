:- [deduction_tree].
:- [op_pri].
:- [m2dot].

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
functor2string(says, ' \\mbox{ \\textsf{says} } ').
functor2string(->, ' \\rightarrow ').
functor2string(:, ' : ').
functor2string(<=, ' \\leq ').
functor2string(s, 'S').

parentheses(Parent_functor, Functor) :-
    op_pri(X, Parent_functor),
    op_pri(Y, Functor), !,
    X \= Y.

proposition2string(_, A, O) :-
    atom(A),
    (wildcard_match('[a-z]_[0-9]*', A) ->
        (sub_string(A, 0, 1, Left, Label), Take is Left - 1, sub_string(A, 2, Take, 0, Index), stringConcat([Label, '_{', Index, '}'], '', O));
        O = A), !.

proposition2string(_, s(X_, A_, Y_), String) :-
    proposition2string(_, X_, X),
    proposition2string(_, A_, A),
    proposition2string(_, Y_, Y),
    stringConcat([X, ' S_', A, ' ', Y], '', String), !.

proposition2string(Parent_functor, B_op, String) :-
    B_op =.. [Functor | Arguments],
    maplist(proposition2string(Functor), Arguments, [A_s, B_s]),
    functor2string(Functor, Functor_s),
    ((B_op =.. [F_, _, _], (F_ = c; F_ = p)) ->
        stringConcat(['\\mbox{{\\bf ', Functor_s, '}}_', A_s, ' ', B_s], '', String), !;
        ((Parent_functor \= :, parentheses(Parent_functor, Functor) ->
            stringConcat(['(', A_s, Functor_s, B_s, ')'], '', String), !;
            stringConcat([A_s, Functor_s, B_s], '', String)))).

print_sequent(Indentation, (Σ, M, Γ_, Δ)) :-
    append([Σ, M, Γ_], Γ),
    maplist(proposition2string(_), Γ, Γ_s),
    maplist(proposition2string(_), Δ, Δ_s),
    join(Γ_s, ', ', Γ_s_j),
    join(Δ_s, ', ', Δ_s_j),
    stringConcat([Indentation, Γ_s_j, ' \\Rightarrow ', Δ_s_j, '~n'], '', Sequent_s),
    format(Sequent_s).

print_tree(Indentation, ([Conclusion, Premises], Rule)) :-
    format('~w\\prooftree~n', Indentation),
    string_concat(Indentation, '\t', Deeper_indentation),
    maplist(print_tree(Deeper_indentation), Premises),
    format('~w\\justifies~n', Indentation),
    print_sequent(Deeper_indentation, Conclusion),
    format('~w\\using~n', Indentation),
    stringConcat([Rule, '~n'], '', Rule_n),
    format(Deeper_indentation), format(Rule_n),
    format('~w\\endprooftree~n', Indentation).

print_leaves(Filename_, ([(_, M, Γ, Δ), []], '')) :-
    gensym(Filename_, Filename__),
    atom_concat(Filename__, '.dot', Filename),
    format('~w\\prooftree~n', ''),
    format('~w\\justifies~n', ''),
    print_sequent('\t', ([], M, Γ, Δ)),
    m2dot(M, Γ, Δ, Filename),
    format('~w\\endprooftree~n', ''), !.

print_leaves(Filename, ([_, Premises], _)) :-
    maplist(print_leaves(Filename), Premises).

latexify(Formula, Filename) :-
    prove(Formula, Sequent),
    tell(Filename),
    format('\\documentclass{article}~n\\pagestyle{empty}~n\\usepackage{amsthm, amsmath, amssymb}~n\\usepackage{prooftree}~n\\begin{document}~n~n\\begin{displaymath}~n'),
    (non_provable ->
        print_leaves(Filename, Sequent);
        print_tree('', Sequent)),
    format('\\end{displaymath}~n~n\\end{document}'),
    told.
