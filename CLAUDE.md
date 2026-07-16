# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
make          # build everything → installs ./vcy
make clean    # remove build artifacts
```

The top-level `Makefile` runs `cd src && dune build` and installs `src/_build/default/run.exe` as `./vcy`. The benchmark test suite lives in `test.sh` (invoked by `make test`).

## Tests

```bash
make test     # benchmark suite (inferred, verify, prepost, movers) + OUnit2 unit tests
```

Requires `cvc5` on `$PATH`. Individual benchmark suites can be run manually:

```bash
./vcy infer benchmarks/inferred/counter.vcy --prover cvc5
./vcy verify benchmarks/verify/even-odd.vcy --prover cvc5
```

OUnit2 tests only (no benchmark files needed):

```bash
cd src && dune runtest
```

## Output organization

Everything a run writes goes under `./veracity_output/run_NNNN/` (with a `latest` symlink), not `/tmp`. Override with `--out-dir DIR` or `$VERACITY_OUT`. When Veracity is driven as a library by a tool above it (ConQuoer), that tool passes `out_dir` in `Veracity.options` and this run nests inside *its* tree instead.

Veracity in turn hands each commute a subdirectory (`commute_NNNN/`) and points Servois2 at it via `Servois2.Util.output_dir`, so the Servois2 queries for a commute land beside the report that describes it. Note `Analyze.phi_of_blocks` allocates that subdir *before* calling `compile_blocks_to_spec`, which writes `veracity_spec.smt` through `Servois2.Util.outfile` — allocate later and the spec escapes into a stray `servois2_output/` tree.

The shared mechanism is `Servois2.Rundir` (`src/servois2/src/rundir.ml`); the root cell for this layer is `Util.output_root`. Each run also writes a `manifest.json` (tool, input, args, result, artifacts, children) using the same schema as the layers above and below.

`Html_output.svgs_of_subdir` inlines *every* `.svg` and `.html` file it finds in a `commute_NNNN/` directory, in sorted order — so dropping a fragment there is all it takes to get it into the report.

### Counterexample model table (`src/analysis/model_table.ml`)

A SAT model comes back in terms of Servois2's state variables, which is not what the user wrote. `Model_table` re-keys it by the expressions appearing in the commute block and writes `expr_table.html` into the commute subdir. See `benchmarks/models/`.

The values come from `Solve.extra_model_exprs`: `Analyze.verify_of_block` sets that ref to a probe for each expression at each state version before the query runs, and Servois2 appends them to its `(get-value ...)` and records the answers in `Solve.extra_models`. Three things constrain what can be probed:

- **Only scalars.** Asking for the value of an array-valued term gets back a `(store ...)`, which Veracity's model parser cannot read — it would abort the run. So `r` is dropped and `r[0]` kept. The test is made against the SMT sorts in `spec.state`, not Veracity types: locals like `r` are absent from `gstates` and would silently infer as `int`.
- **Only the forward run, under `-ae`.** The bowtie encoding declares all five state versions (`""`, `1`, `12`, `2`, `21`) as ordinary constants, so both interleavings can be shown and their disagreement highlighted — that disagreement *is* the counterexample. The AE encoding existentially binds the reversed run to fresh names (`cw2`, `cw21`), leaving the declared `c2`/`c21` unconstrained, so `Model_table.columns ~use_ae` drops those columns rather than reporting junk.
- **Base names, not SSA names.** Probes are built with `exp_to_smt_exp ~indexed:false`, which bypasses the version mangling; the suffix for the state version is applied afterwards. Translating a heap deref also appends to the global `Spec_generator.deref_conds`, so `expr_table` clears it — we are probing, not building a query, and a leftover would be picked up as a conjunct by whoever next drains that global.

## Architecture

Veracity is an OCaml project built with dune. The source lives entirely under `src/`.

### Language pipeline (`src/vcy/`)

| File | Role |
|------|------|
| `vcy_lexer.mll` / `vcy_parser.mly` | Menhir-based lexer/parser → `Ast.prog` |
| `ast.ml` | Core AST types: `prog`, `stmt`, `expr`, `global_env` |
| `interp.ml` | Interpreter; also drives `infer` and `verify` via `Analyze` |
| `vcylib.ml` | Runtime values, environments, built-in operations |
| `run.ml` | CLI entry point; dispatches `parse` / `interp` / `infer` / `verify` / `translate` sub-commands |

### Commutativity analysis (`src/analysis/`)

- `analyze.ml` — translates Veracity ASTs into Servois2 specs and calls the Servois2 library to infer/verify commutativity conditions
- `spec_generator.ml` — generates YAML-format Servois2 specs from `commute` blocks
- `interface.ml` — thin wrapper around the Servois2 OCaml library

Servois2 is a git submodule at `src/servois2`. It is built by the same dune invocation via the `servois2` opam library. Update the submodule pointer in the top-level repo when servois2 changes.

### Parallelism (`src/parallel/`)

`parallel.mli` defines a two-function interface (`create`, `join`). `src/dune` uses a `(select parallel.ml from (domainslib -> parallel_multicore.ml) (-> parallel_singlecore.ml))` stanza inside `(libraries)` to pick the Domain-based implementation when `domainslib` is available (OCaml 5) and fall back to Thread-based otherwise. `parallel_multicore` and `parallel_singlecore` are excluded from the module list; only the selected `parallel.ml` is compiled.

### OCaml API (`src/api/`)

`veracity.mli` / `veracity.ml` expose the full pipeline as a typed library. Inputs are `File of string | Source of string | Prog of Ast.prog`; results are `('a, error) result`. The library is named `vcy` in dune; link with `(libraries vcy)`.

`infer` returns `(Ast.global_env * string option) api_result` — the second element is the path to `index.html` when `opts.html = true`, `None` otherwise. Setting `html = true` in `options` mirrors `--html`: it enables diagram/query output and calls `Html_output.generate` after inference.

### Key dune files

- `src/dune-project` — project root, requires dune ≥ 3.6 and menhir 2.1
- `src/dune` — `(include_subdirs unqualified)` pulls in all subdirectories; excludes `parallel_multicore`, `parallel_singlecore`, and `run` from the library; `run` becomes a standalone executable
- `src/vcy/dune` — declares `ocamllex` and `menhir` rules
- `src/test/dune` — two OUnit2 test executables (`test`, `api_test`) with `LD_LIBRARY_PATH` set for the C hashtable library

## Submodules

```bash
git submodule update --init --recursive   # initialise after clone
git submodule update --remote src/servois2 && git add src/servois2  # bump to latest
```

`src/libhtable` — C cuckoo-hash table used at runtime; also managed as a submodule.

## SMT solvers

`infer` and `verify` require an SMT solver. CVC5 is recommended (`--prover cvc5`); Z3 is also supported (`--prover z3`). The `-ae` flag enables forall/exists mode and is required when the program contains `havoc` statements.

### Timeouts (`src/servois2/src/timeouts.ml`)

All three timeouts live in one shared record, `Servois2.Timeouts.t` — `query` (per SMT check-sat), `synth` (a whole synthesis run, `infer` only), `lattice` (lattice construction, `infer` only). It sits in the bottom layer, like `Rundir`, and every layer above threads it through the existing dependency chain. `Timeouts.speclist` defines the `--timeout-query` / `--timeout-synth` / `--timeout-lattice` flags once, so `servois2`, `vcy` and `conquoer` expose identical names, help and defaults; `--timeout` and `--lattice-timeout` remain as deprecated aliases. Resolution mirrors `Rundir`: caller-supplied (via `Veracity.options.timeouts`, or the CLI mutating `Timeouts.current`) → CLI flag → env var (`SMT_TIMEOUT_*`) → default.

Two design points worth keeping:
- **`query` is enforced by the solver, not SIGALRM.** `Timeouts.prover_args` turns it into each prover's own flag (`--tlimit-per` for CVC5, `-t:` for Z3, `--timeout=` for Yices), appended in `Provers.run_prover`. This is deliberate: there is one `ITIMER_REAL` per process and synthesis already holds it (`Util.run_with_time_limit`), so a per-query SIGALRM would clobber the synth timer. It is also what closes the old holes — CVC5's limit used to be hardcoded, and Z3 had none at all, so it ran unbounded.
- **`default_synth_options` reads `synth`/`lattice` from the record**, so the library default and the CLI default cannot drift — they used to (`lattice` defaulted to `None` in the library but 30s in the CLI, and enabling the lattice without setting it hit an `Option.get`).
