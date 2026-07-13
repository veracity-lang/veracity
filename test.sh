#!/usr/bin/env bash
set -euo pipefail

VCY=${VCY:-./vcy}
pass=0
fail=0

run() {
  local label=$1; shift
  if "$@" > /dev/null 2>&1; then
    echo "  PASS $label"; pass=$((pass+1))
  else
    echo "  FAIL $label"; fail=$((fail+1))
  fi
}

echo "=== benchmarks/inferred ==="
for f in benchmarks/inferred/*.vcy; do
  [[ $f == *tmp.vcy ]] && continue
  run "$f" "$VCY" infer "$f" --prover cvc5
done

echo "=== benchmarks/verify ==="
for f in benchmarks/verify/*.vcy; do
  run "$f" "$VCY" verify "$f" --prover cvc5
done

# These programs are meant to fail verification -- a failing condition is what
# produces a counterexample in the first place, and `verify` exits non-zero for
# it. So the exit status is not the thing to assert; the table is.
run_table() {
  local f=$1
  local d; d=$(mktemp -d)
  "$VCY" verify "$f" --prover cvc5 --html --out-dir "$d" > /dev/null 2>&1 || true
  if [ -n "$(find "$d" -name expr_table.html)" ]; then
    echo "  PASS $f (table)"; pass=$((pass+1))
  else
    echo "  FAIL $f (table)"; fail=$((fail+1))
  fi
  rm -rf "$d"
}

echo "=== benchmarks/models ==="
for f in benchmarks/models/seq-read-after-write.vcy \
         benchmarks/models/array-write-conflict.vcy \
         benchmarks/models/heap-read-after-write.vcy; do
  run_table "$f"
done
# Known limitation: the loop summarisation finds no counterexample, so there is
# no model and no table. Exit status only -- see the header of that file.
run "benchmarks/models/loop-read-after-write.vcy" \
  "$VCY" verify benchmarks/models/loop-read-after-write.vcy --prover cvc5

echo "=== benchmarks/prepost ==="
for f in benchmarks/prepost/*.vcy; do
  run "$f" "$VCY" infer "$f" --prover cvc5
done

MOVERS_INTERP=(
  benchmarks/movers/parse1.vcy
  benchmarks/movers/test-heap-smt1.vcy
  benchmarks/movers/test-heap-write.vcy
  benchmarks/movers/test-interp1.vcy
  benchmarks/movers/test-interp2.vcy
  benchmarks/movers/test-interp3.vcy
)

echo "=== benchmarks/movers (infer) ==="
for f in benchmarks/movers/*.vcy; do
  skip=0
  for i in "${MOVERS_INTERP[@]}"; do [[ $f == $i ]] && skip=1 && break; done
  [[ $skip -eq 1 ]] && continue
  run "$f" "$VCY" infer "$f" --prover cvc5 -ae
done

echo "=== benchmarks/movers (interp) ==="
for f in "${MOVERS_INTERP[@]}"; do
  args=()
  [[ $f == *test-interp3.vcy ]] && args=(3)
  out=$("$VCY" interp "$f" "${args[@]}" 2>&1) || true
  if echo "$out" | grep -q "error occurred\|Fatal error"; then
    echo "  FAIL $f"; fail=$((fail+1))
  else
    echo "  PASS $f"; pass=$((pass+1))
  fi
done

echo "=== benchmarks/loops ==="
for f in benchmarks/loops/*.vcy; do
  run "$f" "$VCY" verify "$f" --prover cvc5
done

echo "=== benchmarks/invariants ==="
for f in benchmarks/invariants/*.vcy; do
  run "$f" "$VCY" invariants "$f" --prover cvc5
done

echo ""
echo "=== Results: $pass passed, $fail failed ==="
exit $((fail > 0 ? 1 : 0))
