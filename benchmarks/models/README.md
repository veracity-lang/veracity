# Counterexample model table

Programs whose commute conditions fail, kept for the table that Veracity writes
when the solver hands back a counterexample.

```bash
./vcy verify benchmarks/models/heap-read-after-write.vcy --prover cvc5 --html
```

Each run writes `expr_table.html` into its `commute_NNNN/` directory, which the
HTML report inlines. Servois2 also emits `heap_table.html`, but its rows are the
SMT *state variables* — reading a counterexample from it means mentally undoing
Veracity's translation. This table is keyed by the expressions actually written
in the commute block:

| Veracity expression | SMT expression | initial | after block 1 | after block 1; block 2 | after block 2 | after block 2; block 1 |
|---|---|---|---|---|---|---|
| `l1->value` | `(select heap_value l1)` | 0 | 1 | 1 | 0 | 1 |
| `x` | `x` | 0 | 0 | **1** | 0 | **0** |

A commutativity counterexample *is* the disagreement between the two
interleavings, so rows whose two final states differ are highlighted: above,
`x` sees the new cell value in one order and the old one in the other.

Both interleavings are only shown under the default bowtie encoding. Under `-ae`
the reversed run is existentially bound to fresh names, leaving the declared
`c2`/`c21` unconstrained, so those columns would report junk and are omitted.

The table is written only when queries are being dumped (`--html` implies it),
and only when a query came back `sat`.

| file | shows |
|---|---|
| `seq-read-after-write.vcy` | the simplest diverging row |
| `array-write-conflict.vcy` | array state: `r` excluded, `r[0]` kept as `(select r 0)` |
| `heap-read-after-write.vcy` | heap derefs mapped back to `l1->value` |
| `loop-read-after-write.vcy` | known limitation: a loop in a commute block yields no counterexample |
