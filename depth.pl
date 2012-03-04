depth(T, 0) :-
    atom(T), !.

depth(T, D) :-
    T =.. [F, L, R],
    depth(L, DL),
    depth(R, DR),
    (member(F, [says, ->]) -> D is max(DL, DR) + 1; D is max(DL, DR)).

max_depth(D, MD) :-
    MD_ is exp(D), MD__ is exp(MD_), MD___ is exp(MD__), MD is exp(MD___).
