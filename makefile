all: op_pri.pl

op_pri.pl: inference_rules_axioms.pl
	@grep "op(.*)." $< | sed 's/.*op(\(.*\),.*, \(.*\))./op_pri(\1, \2)./' > $@

examples/axioms.pl: examples/axioms_l.pl
	cat $< | sed -e "s/latexify(\(.*\), 'examples.*')\./prove(\1)./" > $@

examples/test_HR.pl: examples/test_HR_l.pl
	cat $< | sed -e "s/latexify(\(.*\)/prove(\1/" -e "s/\(.*\), 'examples.*')\./\1)./" > $@

examples/tests.pl: examples/tests_l.pl examples/axioms.pl examples/test_HR.pl
	cat $< | sed -e 's/latexify/deduction_tree/' -e "s/\['\(.*\)_l'\]/\['\1'\]/" > $@

tests: examples/tests.pl
