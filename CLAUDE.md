# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
make          # build everything → installs ./vcy
make clean    # remove build artifacts
```

The top-level `Makefile` drives `src/parallel/Makefile` (which selects the right `parallel.ml` implementation) and then `cd src && dune build`, installing `src/_build/default/run.exe` as `./vcy`.

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

`parallel.mli` defines a two-function interface (`create`, `join`). The `Makefile` in this directory copies either `parallel_singlecore.ml` (Thread-based, default) or `parallel_multicore.ml` (Domain-based, OCaml 5 domains) to `parallel.ml` depending on the running OCaml version. The `parallel_multicore` and `parallel_singlecore` modules are excluded from the main dune library build; only the copied `parallel.ml` is compiled.

### OCaml API (`src/api/`)

`veracity.mli` / `veracity.ml` expose the full pipeline as a typed library. Inputs are `File of string | Source of string | Prog of Ast.prog`; results are `('a, error) result`. The library is named `vcy` in dune; link with `(libraries vcy)`.

### Key dune files

- `src/dune-project` — project root, requires dune ≥ 2.9 and menhir 2.1
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
