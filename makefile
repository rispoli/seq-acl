all: op_pri.pl

op_pri.pl: inference_rules_axioms.pl
	@grep "op(.*)." $< | sed 's/.*op(\(.*\),.*, \(.*\))./op_pri(\1, \2)./' > $@
