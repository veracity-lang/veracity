# Veracity

Veracity is a programming language and tool for reasoning about commutativity of concurrent operations and correctness of loop invariants. Given a program with `commute` blocks and optional `invariant` annotations, Veracity can:

- **infer** the weakest precondition under which two code blocks commute,
- **verify** that an explicitly provided commutativity condition is correct,
- **check invariants** that annotated `while` loop invariants are inductive, or
- **check assertions** that `assert()` statements hold.

## Repository layout

| Path | Contents |
|------|----------|
| `benchmarks/inferred/` | Programs where commutativity conditions are inferred |
| `benchmarks/verify/` | Programs with explicit commutativity conditions to verify |
| `benchmarks/loops/` | Programs with loops inside commute blocks (uses `invariant`) |
| `benchmarks/invariants/` | Loop invariant correctness benchmarks (`./vcy invariants`) |
| `benchmarks/vcgen/` | VCGen benchmarks: assert checking, pre-condition propagation |
| `benchmarks/movers/`, `benchmarks/prepost/` | Mover and pre/post condition examples |
| `src/` | OCaml implementation; build directory |
| `src/api/` | Programmatic OCaml API (`Vcy.Veracity`) |
| `src/test/` | OUnit2 test suites |

## Building

```
make
```

Builds the OCaml sources with dune and installs the `vcy` executable in the repository root.

```
make clean
```

## Prerequisites

A reasonably modern OCaml toolchain with opam:

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

Z3 and Yices are also supported.

## Usage

```
./vcy <command> [flags] <program.vcy>
```

| Command | Description |
|---------|-------------|
| `parse`      | Print the AST of a program |
| `interp`     | Interpret a program |
| `infer`      | Infer commutativity conditions for all `commute _` blocks |
| `verify`     | Verify explicit commutativity conditions |
| `invariants` | Check that `while` loop invariants are inductive |
| `assertions` | Check that `assert()` statements hold |
| `translate`  | Translate to C |

### Common flags

| Flag | Applies to | Description |
|------|-----------|-------------|
| `--prover cvc5` | infer, verify, invariants, assertions | Use CVC5 (default) |
| `--prover z3`   | infer, verify, invariants, assertions | Use Z3 |
| `--prover yices`| infer, verify, invariants, assertions | Use Yices |
| `-ae`           | infer, verify | Forall/exists mode — required when the program contains `havoc` |
| `--timeout N`   | infer, verify | Per-query timeout in seconds |
| `--diagram`     | infer         | Write Servois2 dot/SMT files to disk |
| `--html`        | infer, verify | Generate a self-contained HTML report in `/tmp/` |
| `--htmlopen`    | infer, verify | Like `--html`, and open the report in the browser |
| `-q`            | infer, verify | Quiet: print conditions only |
| `--silent`      | infer, verify | Suppress all stdout output |
| `--force`       | infer         | Re-infer even when a condition is already provided |

### Examples

Infer commutativity conditions:

```
./vcy infer benchmarks/prepost/pre.vcy --prover cvc5
```

Verify an explicit condition:

```
./vcy verify benchmarks/verify/even-odd.vcy --prover cvc5
```

Verify commutativity of operations that contain loops (requires `invariant` annotation on the loop):

```
./vcy verify benchmarks/loops/scan.vcy --prover cvc5
```

Check that loop invariants are inductive:

```
./vcy invariants benchmarks/invariants/inc.vcy --prover cvc5
```

Check that assertions hold:

```
./vcy assertions benchmarks/vcgen/assert.vcy --prover cvc5
```

Interpret a program with arguments:

```
./vcy interp benchmarks/movers/counter.vcy 5
```

## Language features

### Commute blocks

```
commute _ {          // infer the condition
    { block_A }
    { block_B }
}

commute (x > 0) {   // verify this condition
    { block_A }
    { block_B }
}
```

Variants for left/right mover analysis: `commute_left`, `commute_right`, `commute_left_ctx <ctx>`, `commute_right_ctx <ctx>`.

### Loop invariants

Annotate a `while` loop with `invariant` to enable commutativity reasoning about loop bodies:

```
while (i < n) invariant i >= 0 && i <= n {
    i = i + 1;
}
```

When a commute block contains a loop, the invariant is used by the SMT encoding to represent the loop's net effect. The `invariants` command separately checks that the invariant is inductive.

## Testing

```
make test
```

Runs all benchmark suites (inferred, verify, prepost, movers, loops, invariants, vcgen) and the OUnit2 unit tests.

## OCaml API

Veracity exposes a programmatic OCaml API via the `Vcy.Veracity` module, so you can parse, interpret, infer, verify, and check programs directly from OCaml without shelling out to the CLI. See [API.md](API.md) for full documentation.

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
