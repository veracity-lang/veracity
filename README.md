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

opam install sexplib ppxlib.0.22.0+effect-syntax ppx_deriving_yaml
eval $(opam env)
```

# Usage

Build with `make` in `veracity/src/`

Clean with `make clean` in `veracity/src/`

Execute Veracity with `veracity/src/vcy.exe`. This will display the available commands.

Example of execution:

    veracity/src/vcy.exe interp bench/manuals/dihedral.vcy 10 5 0 2 1

# Notes

The `libcuckoo` hashtable has been omitted from this codebase. Veracity programs which use the `libcuckoo` hashtable variant will default to the naïvely concurrent OCaml variant.
