CC=/usr/bin/g++
CFLAGS=-W -Wall -Wextra -Werror -pedantic -ansi -O2
ARGTABLE_PATH=./argtable2
ARGTABLEI=-I$(ARGTABLE_PATH)/include
ARGTABLEL=$(ARGTABLE_PATH)/lib
ARGTABLEO=$(ARGTABLEL)/libargtable2.a
LDFLAGS=-L$(ARGTABLEL)

all: server client

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
