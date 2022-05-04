#
# Makefile for the malloc lab driver
#

VERSION=std
CC = gcc
CFLAGS = -O2 -g -DDRIVER
# disable flag during dev
MMFLAGS = -Wall -Wextra -Werror

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o driverlib.o

all: mdriver

mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h driverlib.h
memlib.o: memlib.c memlib.h
mm.o: mm-$(VERSION).c mm.h memlib.h
	$(CC) $(MMFLAGS) $(CFLAGS) -o mm.o -c mm-$(VERSION).c
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
driverlib.o: driverlib.c driverlib.h

clean:
	rm -f *~ *.o mdriver



