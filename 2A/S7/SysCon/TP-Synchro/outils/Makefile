BINAIRES = taillenoyau

CFLAGS = -I ../include

all : $(BINAIRES)

clean :
	rm -f $(BINAIRES) *.o

.c.o :
	gcc $(CFLAGS) -c $<
