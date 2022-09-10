#!/usr/bin/env sh
export BENCHMARKS_RUNNER=TRUE
export BENCH_LIB="vec_bench"
exec dune exec --release -- "bench/bench_main.exe" -fork -run-without-cross-library-inlining "$@"
