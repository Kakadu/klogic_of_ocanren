all: quines_bench_racket.sexp

quines_bench.exe: quines_bench.rkt
	@$(RM) $@
	raco exe -v --cs -o $@ $^

.PHONY: quines_bench_racket.sexp
quines_bench_racket.sexp: quines_bench.exe
	@ $(RM) $@
	sudo cpupower frequency-set --governor performance
	taskset -c 0 ./$^

clean:
	$(RM) numero_bench_racket.sexp* quines_bench.exe
