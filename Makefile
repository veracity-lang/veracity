all:
	cd src && dune build && cp vcy.exe ..

clean:
	cd src && make clean
