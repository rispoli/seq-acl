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
