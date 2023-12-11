CC=clang
CCXX=clang++
FLAGS=-std=c++17 -m32 -g2 -fstack-protector-all -O3

all: freqanalyzer.o
	$(CCXX) $(FLAGS) -o freqanalyzer freqanalyzer.o

freqanalyzer.o: freqanalyzer.cpp
	$(CCXX) $(FLAGS) -c -o freqanalyzer.o -g freqanalyzer.cpp

clean:
	$(RM) *.a *.o *~ freqanalyzer
