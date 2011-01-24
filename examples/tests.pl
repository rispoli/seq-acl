:- ['../latexify.pl'].

:- [test_defLIS2010].

?- latexify(([x], [], [], [x : []('A', '\\alpha') -> []('B', []('A', '\\alpha'))]), 'examples/v01.tex').
?- latexify(([x, y], [x <= y], [x : []('A', '\\alpha')], [y : []('A', '\\alpha')]), 'examples/v02.tex').
?- latexify(([x], [], [], [x : (([]('A', '\\varphi') -> '\\varphi') and ([]('A', []('B', '\\varphi') -> '\\varphi')) and []('B', '\\varphi')) -> '\\varphi']), 'examples/v03.tex').
?- latexify(([x], [], [x : []('A', '\\varphi') -> '\\varphi', x : []('A', '\\varphi')], [x : '\\varphi']), 'examples/v04.tex').
?- latexify(([x], [], [x : []('A', []('B', '\\varphi') -> '\\varphi'), x : []('B', '\\varphi')], [x : []('A', '\\varphi')]), 'examples/v05.tex').
?- latexify(([x], [], [x : []('A', '\\alpha' -> '\\beta'), x : []('A', '\\alpha')], [x : []('A', '\\beta')]), 'examples/v06.tex').
?- latexify(([x], [], [x : []('A', '\\alpha') -> '\\alpha', x : []('A', '\\alpha')], [x : '\\alpha']), 'examples/v07.tex').
?- latexify(([x], [], [x : []('A', []('B', '\\alpha')) -> '\\alpha', x : []('A', []('B', '\\alpha'))], [x : '\\alpha']), 'examples/v08.tex').
?- latexify(([x], [], [x : []('A', '\\alpha') -> '\\beta', x : []('A', '\\alpha')], [x : []('A', '\\beta')]), 'examples/v13.tex').
