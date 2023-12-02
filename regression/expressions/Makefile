TESTS=$(sort $(basename $(wildcard generated*.lama)))

RC = ../../src/lamac

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "regression/expressions/$@"
	@LAMA=../../runtime $(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
	@cat $@.input | LAMA=../../runtime $(RC) -i $< > $@.log && diff $@.log orig/$@.log
	@cat $@.input | LAMA=../../runtime $(RC) -s $< > $@.log && diff $@.log orig/$@.log
	@LAMA=../../runtime $(RC) -b $< && cat $@.input | ../../interp/interp ./$@.bc 2> /dev/null > $@.log && diff $@.log orig/$@.log

clean:
	rm -f *.log *.s *.bc *~
	find . -maxdepth 1 -type f -not -name '*.*' -not -name 'Makefile' -delete

