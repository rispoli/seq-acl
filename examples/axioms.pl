?- prove('A' says ('\\varphi' -> '\\psi') -> 'A' says '\\varphi' -> 'A' says '\\psi').
?- prove('A' says '\\varphi' -> 'B' says ('A' says '\\varphi')).
?- prove(c('A', '\\varphi' -> '\\psi') -> (c('A', '\\varphi') -> c('A', '\\psi'))).
?- prove(c('A', '\\varphi') -> p('A', '\\varphi')).
?- prove(p('A', '\\varphi' or '\\psi') -> p('A', '\\varphi') or p('A', '\\psi')).
?- prove((c('A', '\\varphi') and ('A' says c('B', '\\varphi'))) -> c('B', '\\varphi')).
?- prove(('A' ratified '\\varphi') -> ('A' says '\\varphi')).
?- prove(('A' ratified ('\\varphi' -> '\\psi')) -> ('A' ratified '\\varphi') -> ('A' ratified '\\psi')).
?- prove(('A' ratified '\\varphi') -> 'B' says 'A' says '\\varphi').
