% Axioms of Intuitionistic Propositional Logic

?- prove('\\bot' -> '\\varphi').
?- prove(('\\varphi' -> '\\psi') -> (('\\chi' -> '\\psi') -> (('\\varphi' or '\\psi') -> '\\psi'))).
?- prove('\\chi' -> ('\\varphi' or '\\chi')).
?- prove('\\varphi' -> ('\\varphi' or '\\chi')).
?- prove('\\varphi' -> ('\\chi' -> ('\\varphi' and '\\chi'))).
?- prove(('\\varphi' and '\\chi') -> '\\chi').
?- prove(('\\varphi' and '\\chi') -> '\\varphi').
?- prove(('\\varphi' -> ('\\chi' -> '\\psi')) -> (('\\varphi' -> '\\chi') -> ('\\varphi' -> '\\psi'))).
?- prove('\\varphi' -> ('\\chi' -> '\\varphi')).

% Axioms for Modal Primitives

?- prove('A' says ('\\varphi' -> '\\psi') -> 'A' says '\\varphi' -> 'A' says '\\psi').
?- prove('A' says '\\varphi' -> 'B' says ('A' says '\\varphi')).
