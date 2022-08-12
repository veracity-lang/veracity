
# OS Flag detection modified from https://gist.github.com/sighingnow/deee806603ec9274fd47:
# Original Author: He Tao

OSFLAG 				:=
ifeq ($(OS),Windows_NT)
	OSFLAG=WIN32
else
	UNAME_S:=$(shell uname -s)
	ifeq ($(UNAME_S),Linux)
		OSFLAG=LINUX
	endif
	ifeq ($(UNAME_S),Darwin)
		OSFLAG=OSX
	endif
endif

# Extension creation:
EXT :=
ifeq ($(OSFLAG),WIN32)
	EXT=so
else 
	ifeq ($(OSFLAG),LINUX)
		EXT=so
	endif
	ifeq ($(OSFLAG),OSX)
		EXT=dylib
	endif
endif

SUBDIRS := analysis parallel util vcy
BUILDDIR := _build
EXECNAME := vcy.exe

all:
	for dir in $(SUBDIRS); do \
        $(MAKE) -C $$dir; \
    done
	dune build
	mv run.exe $(EXECNAME)

clean:
	for dir in $(SUBDIRS); do \
        $(MAKE) -C $$dir clean; \
    done
	dune clean
	rm -f $(EXECNAME)

.PHONY:
	echo $(EXT)
	echo $(OSFLAG)

test: all
	dune runtest
