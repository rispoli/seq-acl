CC=/usr/bin/g++
CFLAGS=-W -Wall -Wextra -Werror -pedantic -ansi -O2
ARGTABLE_PATH=./argtable2
ARGTABLEI=-I$(ARGTABLE_PATH)/include
ARGTABLEL=$(ARGTABLE_PATH)/lib
ARGTABLEO=$(ARGTABLEL)/libargtable2.a
LDFLAGS=-L$(ARGTABLEL)

SRCS=$(wildcard *.cpp)
PSRCS=$(wildcard *.pl)
EXECS=$(SRCS:%.cpp=%)

GNU_FOLDER=.gnu_translation

all: $(EXECS) credentials.gnu

%.o: %.cpp message.h
	$(CC) $(CFLAGS) -c $(ARGTABLEI) $< -o $@

$(EXECS): %: %.o
	$(CC) $(LDFLAGS) $< $(ARGTABLEO) -o $@

credentials.gnu: $(PSRCS)
	@mkdir $(GNU_FOLDER)
	@cp gnu_prolog_toplevel.pl $(GNU_FOLDER)
	@cp gnu_prolog_utilities.pl $(GNU_FOLDER)
	@cat credentials.pl | sed -e "s|:- \[\(.*\)\].|:- include('\1').|" -e 's/format(atom(\(.*\)), \(.*\), \(.*\))/format_to_atom(\1, \2, [\3])/' -e s/string_concat/atom_concat/ > $(GNU_FOLDER)/credentials.pl
	@echo -e "\n:- include('gnu_prolog_utilities')." >> $(GNU_FOLDER)/credentials.pl
	@cat prove.pl | sed -e "s|:- \[\(.*\)\].|:- include('\1').|" -e s/Σ/Sigma/g -e s/Γ/Gamma/g -e s/Δ/Delta/g -e s/\s*reset_gensym,// -e s/assert/asserta/ > $(GNU_FOLDER)/prove.pl
	@cat inference_rules.pl | sed -e 's/\(:-\)\? \+\(op(.*)\)./:- \2./' -e s/Σ/Sigma/g -e s/Γ/Gamma/g -e s/Δ/Delta/g -e s/include/filter/g -e "s|:- \[\(.*\)\].|:- include('\1').|" > $(GNU_FOLDER)/inference_rules.pl
	@cp principals.pl $(GNU_FOLDER)/principals.pl
	@cp depth_distance.pl $(GNU_FOLDER)/depth_distance.pl
	@cat abducibles.pl | sed -e s/list_to_set/sort/g > $(GNU_FOLDER)/abducibles.pl
	@cat countermodels.pl | sed -e s/list_to_set/sort/g -e s/Σ/Sigma/g -e s/Γ/Gamma/g -e s/Δ/Delta/g > $(GNU_FOLDER)/countermodels.pl
	@cat grounder.pl | sed -e 's/\(:-\)\? \+\(op(.*)\)./:- \2./' -e s/list_to_set/sort/g -e s/include/filter/g > $(GNU_FOLDER)/grounder.pl
	cd $(GNU_FOLDER); gplc --no-top-level -o ../credentials.gnu gnu_prolog_toplevel.pl
	@rm -r $(GNU_FOLDER)

clean:
	-rm -f *.o $(EXECS) credentials.gnu
