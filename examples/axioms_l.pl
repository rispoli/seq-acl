?- latexify('A' says ('\\varphi' -> '\\psi') -> 'A' says '\\varphi' -> 'A' says '\\psi', 'examples/K-S.tex').
?- latexify('A' says '\\varphi' -> 'B' says ('A' says '\\varphi'), 'examples/I-SS.tex').
?- latexify(c('A', '\\varphi' -> '\\psi') -> (c('A', '\\varphi') -> c('A', '\\psi')), 'examples/K-C.tex').
?- latexify(c('A', '\\varphi') -> p('A', '\\varphi'), 'examples/C2P.tex').
?- latexify(p('A', '\\varphi' or '\\psi') -> p('A', '\\varphi') or p('A', '\\psi'), 'examples/or-P.tex').
?- latexify((c('A', '\\varphi') and ('A' says c('B', '\\varphi'))) -> c('B', '\\varphi'), 'examples/del-C.tex').
?- latexify(('A' ratified '\\varphi') -> ('A' says '\\varphi'), 'examples/RS.tex').
?- latexify(('A' ratified ('\\varphi' -> '\\psi')) -> ('A' ratified '\\varphi') -> ('A' ratified '\\psi'), 'examples/K-R.tex').
?- latexify(('A' ratified '\\varphi') -> 'B' says 'A' says '\\varphi', 'examples/R-I-SS.tex').
