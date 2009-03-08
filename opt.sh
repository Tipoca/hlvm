llc -f aout.bc -o aout.s
gcc -lsigsegv aout.s -o aout
opt -std-compile-opts <aout.bc >aoutopt.bc
llc -f aoutopt.bc -o aoutopt.s
gcc -lsigsegv aoutopt.s -o aoutopt
