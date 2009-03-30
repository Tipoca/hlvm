llc -tailcallopt -f aout.bc -o aout.s
gcc -lsigsegv -ldl -lm aout.s -o aout
gcc -p -lsigsegv -ldl -lm aout.s -o aoutprof
opt -std-compile-opts <aout.bc >aoutopt.bc
llc -tailcallopt -f aoutopt.bc -o aoutopt.s
gcc -lsigsegv -ldl -lm aoutopt.s -o aoutopt
