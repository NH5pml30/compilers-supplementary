CC=gcc
CCXX=g++
FLAGS=-m32 -g2 -fstack-protector-all -O3 -DNDEBUG
# FLAGS=-m32 -g2 -fstack-protector-all -O0 -DDEBUG

all: interp.o interp_util.s gc.o runtime.o
	$(CCXX) $(FLAGS) -o interp interp.o interp_util.s gc.o runtime.o

gc.o: ../runtime/gc.c ../runtime/gc.h
	$(CC) -rdynamic $(FLAGS) -DLAMA_ENV -c ../runtime/gc.c

runtime.o: ../runtime/runtime.c ../runtime/runtime.h
	$(CC) $(FLAGS) -DLAMA_ENV -c ../runtime/runtime.c

interp.o: interp.cpp
	$(CCXX) $(FLAGS) -c -o interp.o -g interp.cpp

clean:
	$(RM) *.a *.o *~ interp
