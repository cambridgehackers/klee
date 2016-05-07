#
set -x
#./unittests/Solver/Debug+Asserts/SolverTests --debug-dump-stp-queries
./Debug+Asserts/bin/klee -print-after-all -print-before-all -log-partial-queries-early -debug-dump-stp-queries -debug-print-instructions jtest/connect.bc BAba
