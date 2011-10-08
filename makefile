CC=/usr/bin/g++
CFLAGS=-W -Wall -Wextra -Werror -pedantic -ansi -O2
ARGTABLE_PATH=./argtable2
ARGTABLEI=-I$(ARGTABLE_PATH)/include
ARGTABLEL=$(ARGTABLE_PATH)/lib
ARGTABLEO=$(ARGTABLEL)/libargtable2.a
LDFLAGS=-L$(ARGTABLEL)

SRCS=$(wildcard *.cpp)
EXECS=$(SRCS:%.cpp=%)

all: $(EXECS)

%.o: %.cpp message.h
	$(CC) $(CFLAGS) -c $(ARGTABLEI) $< -o $@

$(EXECS): %: %.o
	$(CC) $(LDFLAGS) $< $(ARGTABLEO) -o $@

clean:
	-rm -f *.o $(EXECS)
