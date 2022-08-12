parallel_singlecore_file = parallel_singlecore.ml
parallel_multicore_file  = parallel_multicore.ml

ocaml_switch_multicore   = 4.12.0+domains+effects

parallel_module := $(shell \
	if [ $(shell ocamlc --version) = $(ocaml_switch_multicore) ]; \
	then echo $(parallel_multicore_file); \
	else echo $(parallel_singlecore_file); fi \
)

all:
	cp $(parallel_module) parallel.ml

clean:
	rm -f parallel.ml