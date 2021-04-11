SHELL = /bin/bash

bench-z3:
	OUT=bench-z3; \
	> $$OUT; \
	for file in */*.smt2; do \
		echo "$$ z3 $$file" | tee -a $$OUT; \
		(time z3 "$$file" -T:3) 2>&1 | tee -a $$OUT; \
		echo "" | tee -a $$OUT; \
	done
