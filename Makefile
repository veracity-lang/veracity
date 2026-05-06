VCY := ./vcy.exe

INFERRED_TESTS := $(filter-out benchmarks/inferred/tmp.vcy, \
    $(wildcard benchmarks/inferred/*.vcy))

VERIFY_TESTS := $(wildcard benchmarks/verify/*.vcy)

MOVERS_INTERP_TESTS := \
    benchmarks/movers/parse1.vcy \
    benchmarks/movers/test-heap-smt1.vcy \
    benchmarks/movers/test-heap-write.vcy \
    benchmarks/movers/test-interp1.vcy \
    benchmarks/movers/test-interp2.vcy \
    benchmarks/movers/test-interp3.vcy

MOVERS_INFER_TESTS := $(filter-out $(MOVERS_INTERP_TESTS), \
    $(wildcard benchmarks/movers/*.vcy))

all:
	cd src && dune build && cp vcy.exe ..

test: all
	@pass=0; fail=0; \
	echo "=== benchmarks/inferred ==="; \
	for f in $(INFERRED_TESTS); do \
		if $(VCY) infer "$$f" --prover cvc5 > /dev/null 2>&1; then \
			echo "  PASS $$f"; pass=$$((pass+1)); \
		else \
			echo "  FAIL $$f"; fail=$$((fail+1)); \
		fi; \
	done; \
	echo "=== benchmarks/verify ==="; \
	for f in $(VERIFY_TESTS); do \
		if $(VCY) verify "$$f" --prover cvc5 > /dev/null 2>&1; then \
			echo "  PASS $$f"; pass=$$((pass+1)); \
		else \
			echo "  FAIL $$f"; fail=$$((fail+1)); \
		fi; \
	done; \
	echo "=== benchmarks/movers (infer) ==="; \
	for f in $(MOVERS_INFER_TESTS); do \
		if $(VCY) infer "$$f" --prover cvc5 -ae > /dev/null 2>&1; then \
			echo "  PASS $$f"; pass=$$((pass+1)); \
		else \
			echo "  FAIL $$f"; fail=$$((fail+1)); \
		fi; \
	done; \
	echo "=== benchmarks/movers (interp) ==="; \
	for f in $(MOVERS_INTERP_TESTS); do \
		args=""; [ "$$f" = "benchmarks/movers/test-interp3.vcy" ] && args="3"; \
		out=$$($(VCY) interp "$$f" $$args 2>&1); \
		if echo "$$out" | grep -q "error occurred\|Fatal error"; then \
			echo "  FAIL $$f"; fail=$$((fail+1)); \
		else \
			echo "  PASS $$f"; pass=$$((pass+1)); \
		fi; \
	done; \
	echo ""; \
	echo "=== Results: $$pass passed, $$fail failed ==="; \
	test $$fail -eq 0

clean:
	cd src && make clean
	rm -f servois2_diagram*
	rm -f servois2_query*
	rm -f servois2_result*
