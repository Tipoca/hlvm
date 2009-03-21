llc -f aout.bc -o aout.s
gcc -lsigsegv -ldl -lm aout.s -o aout
opt -std-compile-opts <aout.bc >aoutopt.bc
llc -f aoutopt.bc -o aoutopt.s
gcc -lsigsegv -ldl -lm aoutopt.s -o aoutopt
