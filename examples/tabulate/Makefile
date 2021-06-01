WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib

all: example.mlw

preexample.mlw: example.rl biexample.rl
	$(WHYREL) -o $@ $^

example.mlw: preexample.mlw
	python3 post-process.py $< > $@

type: example.rl biexample.rl
	$(WHYREL) -type-check -debug $^

ide: example.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f preexample.mlw
	rm -f example.mlw
