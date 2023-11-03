# Directories

`benchmarks` contains the test case programs used in the official Veracity paper.

`examples` contains additional test programs of general Veracity functionality. Many of these programs include features impleemnted in the Veracity interpreter, but not yet a part of our inference/verification logic.

`reports` contains utilities for generating tables of results from running test cases.

`src` contains the implementation of Veracity, and is the build directory and location of the `vcy.exe` executable.

# Preparation

These instructions assume the user is working with a fresh install of `Ubuntu 20.04`.

```
add-apt-repository ppa:avsm/ppa
apt update
apt install opam
apt install cvc4

opam init
eval $(opam env)

opam update
opam switch create 4.12.0mc 4.12.0+domains+effects --repositories=multicore=git+https://github.com/ocaml-multicore/multicore-opam.git,default
opam switch 4.12.0mc
eval $(opam env)

opam install sexplib ppxlib.0.22.0+effect-syntax ppx_deriving_yaml ounit2 menhir
eval $(opam env)
```

# Usage

Build with `make` in `src/`

Clean with `make clean` in `src/`

Execute Veracity with `src/vcy.exe`. This will display the available commands.

Example of execution:

    src/vcy.exe interp benchmarks/manual/dihedral.vcy 10 5 0 2 1
