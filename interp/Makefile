FLAGS=-m32 -g2 -fstack-protector-all

all: interp.o interp_util.s virt_stack.o gc.o runtime.o
	$(CCXX) $(FLAGS) -o interp interp.o interp_util.s virt_stack.o gc.o runtime.o

virt_stack.o: ../runtime/virt_stack.h ../runtime/virt_stack.c
	$(CC) $(FLAGS) -DLAMA_ENV -c ../runtime/virt_stack.c

gc.o: ../runtime/gc.c ../runtime/gc.h
	$(CC) -rdynamic $(FLAGS) -DLAMA_ENV -c ../runtime/gc.c

runtime.o: ../runtime/runtime.c ../runtime/runtime.h
	$(CC) $(FLAGS) -DLAMA_ENV -c ../runtime/runtime.c

interp.o: interp.cpp
	$(CCXX) $(FLAGS) -c -o interp.o -g interp.cpp

clean:
	$(RM) *.a *.o *~ interp
