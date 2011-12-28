:- initialization(prove_c).
:- include('credentials').

a2t(A, T) :-
    atom_concat(A, '.', A_),
    read_from_atom(A_, T).

prove_c :-
    argument_counter(N),
    ((N == 4) ->
        (argument_list([PF, P, R_]), a2t(R_, R), prove_c(PF, P, R));
        ((N == 5) ->
            (argument_list([PF, P, C_, R_]), a2t(C_, C), a2t(R_, R), prove_c(PF, P, C, R));
            print('Usage:\n\tcredentials.gnu <policy_file> principal request\n or:\n\tcredentials.gnu <policy_file> principal credentials request\n'))).
