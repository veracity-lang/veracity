# Veracity

Veracity is a programming language and tool for reasoning about commutativity of concurrent operations. Given a program with `commute` blocks, Veracity can:

- **infer** the weakest precondition under which two code blocks commute, or
- **verify** that an explicitly provided condition is correct.

## Repository layout

| Path | Contents |
|------|----------|
| `benchmarks/` | Test programs (inferred, verify, movers, prepost, …) |
| `src/` | OCaml implementation; build directory |
| `src/api/` | Programmatic OCaml API (`Vcy.Veracity`) |
| `src/test/` | OUnit2 test suites |
| `reports/` | Utilities for generating result tables |

## Building

```
make
```

This builds the OCaml sources with dune and installs the `vcy` executable in the repository root.

```
make clean
```

## Prerequisites

The instructions below assume a reasonably modern OCaml toolchain with opam.

```bash
opam install dune menhir ounit2 str
```

Veracity uses [Servois2](https://github.com/jdublu10/servois2) as its SMT back-end (included as a submodule). You also need at least one SMT solver — **CVC5 is recommended**:

```bash
# macOS
brew install cvc5

# Ubuntu
apt install cvc5
```

## Usage

```
./vcy <command> [flags] <program.vcy>
```

| Command | Description |
|---------|-------------|
| `parse`     | Print the AST of a program |
| `interp`    | Interpret a program |
| `infer`     | Infer commutativity conditions for all `commute _` blocks |
| `verify`    | Verify explicit commutativity conditions |
| `translate` | Translate to C |

### Common flags

| Flag | Applies to | Description |
|------|-----------|-------------|
| `--prover cvc5` | infer, verify | Use CVC5 (recommended) |
| `--prover z3`   | infer, verify | Use Z3 |
| `-ae`           | infer, verify | Forall/exists mode — required when the program contains `havoc` |
| `--timeout N`   | infer, verify | Per-query timeout in seconds |
| `--diagram`     | infer         | Write Servois2 dot/SMT files to disk |
| `--html`        | infer         | Generate a self-contained HTML report |
| `-q`            | infer, verify | Quiet: print conditions only |

### Examples

Infer commutativity conditions:

```
./vcy infer benchmarks/prepost/pre.vcy --prover cvc5
```

Verify an explicit condition:

```
./vcy verify benchmarks/verify/even-odd.vcy --prover cvc5
```

Interpret a program with arguments:

```
./vcy interp benchmarks/movers/counter.vcy 5
```

## Testing

```
make test
```

Runs all benchmark suites (inferred, verify, prepost, movers) and the OUnit2 unit tests.

## OCaml API

Veracity exposes a programmatic OCaml API via the `Vcy.Veracity` module, so you can parse, interpret, infer, and verify programs directly from OCaml without shelling out to the CLI. See [API.md](API.md) for full documentation.

Quick example:

```ocaml
open Vcy

let () =
  match Veracity.infer ~opts:{ Veracity.default_options with prover = `CVC5 }
          (Veracity.File "benchmarks/prepost/pre.vcy") with
  | Ok _g   -> print_endline "Inference succeeded"
  | Error e -> Printf.eprintf "Error: %s\n" (match e with
      | Veracity.InferError s -> s | _ -> "other")
```
