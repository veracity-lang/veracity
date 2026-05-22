all:
	cd src && dune build
	install -m 755 src/_build/default/run.exe vcy

test: all
	./test.sh

clean:
	cd src && dune clean
