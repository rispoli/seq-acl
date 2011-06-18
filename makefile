CC=/usr/bin/g++
CFLAGS=-W -Wall -Wextra -Werror -pedantic -ansi -O2
ARGTABLE_PATH=./argtable2
ARGTABLEI=-I$(ARGTABLE_PATH)/include
ARGTABLEL=$(ARGTABLE_PATH)/lib
ARGTABLEO=$(ARGTABLEL)/libargtable2.a
LDFLAGS=-L$(ARGTABLEL)

all: op_pri.pl server client

op_pri.pl: inference_rules_axioms.pl
	@grep "op(.*)." $< | sed 's/.*op(\(.*\),.*, \(.*\))./op_pri(\1, \2)./' > $@

examples/axioms.pl: examples/axioms_l.pl
	cat $< | sed -e "s/latexify(\(.*\), 'examples.*')\./prove(\1)./" > $@

examples/test_HR.pl: examples/test_HR_l.pl
	cat $< | sed -e "s/latexify(\(.*\)/prove(\1/" -e "s/\(.*\), 'examples.*')\./\1)./" > $@

examples/tests.pl: examples/tests_l.pl examples/axioms.pl examples/test_HR.pl
	cat $< | sed -e 's/latexify/deduction_tree/' -e "s/\['\(.*\)_l'\]/\['\1'\]/" > $@

tests: examples/tests.pl

server.o: server.cpp message.h
	$(CC) $(CFLAGS) -c $(ARGTABLEI) $< -o $@

server: server.o
	$(CC) $(LDFLAGS) $< $(ARGTABLEO) -o $@

client.o: client.cpp message.h
	$(CC) $(CFLAGS) -c $(ARGTABLEI) $< -o $@

client: client.o
	$(CC) $(LDFLAGS) $< $(ARGTABLEO) -o $@

clean:
	-rm -f server.o server client.o client
