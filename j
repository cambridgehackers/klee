#
set -x
#./unittests/Solver/Debug+Asserts/SolverTests --debug-dump-stp-queries
#./Debug+Asserts/bin/klee -print-after-all -print-before-all -log-partial-queries-early -debug-dump-stp-queries jtest/connect.bc Aba
#./Debug+Asserts/bin/klee -print-after-all -print-before-all -log-partial-queries-early -debug-dump-stp-queries jtest/connect.bc BBB
./Debug+Asserts/bin/klee -log-partial-queries-early -debug-dump-stp-queries jtest/connect.bc BBB
