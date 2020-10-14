OCB = ocamlbuild
INCLUDES = src
OCB_FLAGS = -Is $(INCLUDES) -use-ocamlfind -use-menhir -yaccflags --explain
EXECUTABLE = src/main.native
PAGER ?= cat
PARSER = src/parser.mly

all: main.native

.PHONY: main.native
main.native:
	$(OCB) $(OCB_FLAGS) $(EXECUTABLE)
	mkdir -p bin
	cp -L main.native bin/whyrel

explain:
	$(PAGER) _build/src/parser.conflicts

menhir-repl:
	menhir --interpret --interpret-show-cst --interpret-error $(PARSER)

.PHONY: clean
clean:
	$(OCB) -clean
	rm -f bin/whyrel

