WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib

all: fact.mlw

prefact.mlw: fact.rl
	$(WHYREL) -margin 136 -o $@ $^

fact.mlw: prefact.mlw
	python3 post-process.py $< > $@

ide: fact.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f prefact.mlw
	rm -f fact.mlw
