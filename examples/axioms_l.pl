% Axioms of Intuitionistic Propositional Logic

?- latexify('\\bot' -> '\\varphi', 'examples/false.tex').
?- latexify(('\\varphi' -> '\\psi') -> (('\\chi' -> '\\psi') -> (('\\varphi' or '\\psi') -> '\\psi')), 'examples/or.3.tex').
?- latexify('\\chi' -> ('\\varphi' or '\\chi'), 'examples/or.2.tex').
?- latexify('\\varphi' -> ('\\varphi' or '\\chi'), 'examples/or.1.tex').
?- latexify('\\varphi' -> ('\\chi' -> ('\\varphi' and '\\chi')), 'examples/and.3.tex').
?- latexify(('\\varphi' and '\\chi') -> '\\chi', 'examples/and.2.tex').
?- latexify(('\\varphi' and '\\chi') -> '\\varphi', 'examples/and.1.tex').
?- latexify(('\\varphi' -> ('\\chi' -> '\\psi')) -> (('\\varphi' -> '\\chi') -> ('\\varphi' -> '\\psi')), 'examples/then.2.tex').
?- latexify('\\varphi' -> ('\\chi' -> '\\varphi'), 'examples/then.1.tex').

% Axioms for Modal Primitives

?- latexify('A' says ('\\varphi' -> '\\psi') -> 'A' says '\\varphi' -> 'A' says '\\psi', 'examples/K-S.tex').
?- latexify('A' says '\\varphi' -> 'B' says ('A' says '\\varphi'), 'examples/I-SS.tex').
?- latexify(c('A', '\\varphi' -> '\\psi') -> (c('A', '\\varphi') -> c('A', '\\psi')), 'examples/K-C.tex').
?- latexify(c('A', '\\varphi') -> p('A', '\\varphi'), 'examples/C2P.tex').
?- latexify(p('A', '\\varphi' or '\\psi') -> p('A', '\\varphi') or p('A', '\\psi'), 'examples/or-P.tex').
?- latexify((c('A', '\\varphi') and ('A' says c('B', '\\varphi'))) -> c('B', '\\varphi'), 'examples/del-C.tex').
?- latexify(('A' ratified '\\varphi') -> ('A' says '\\varphi'), 'examples/RS.tex').
?- latexify(('A' ratified ('\\varphi' -> '\\psi')) -> ('A' ratified '\\varphi') -> ('A' ratified '\\psi'), 'examples/K-R.tex').
?- latexify(('A' ratified '\\varphi') -> 'B' says 'A' says '\\varphi', 'examples/R-I-SS.tex').
