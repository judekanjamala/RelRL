WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
THEORY_DIR=.
POST_PROCESS=../../util/post-process.sed

all: listpub.mlw

prelistpub.mlw: listpub.rl
	$(WHYREL) -margin 80 -o $@ $^

listpub.mlw: prelistpub.mlw
	python3 post-process.py $< > $@

ide: listpub.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) -L $(THEORY_DIR) $<

type: listpub.rl
	$(WHYREL) -type-check -debug $^

theory: listpub_theory.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) -L $(THEORY_DIR) $<

check: listpub.mlw
	$(WHY3) prove -L $(WHYREL_STDLIB) -L $(THEORY_DIR) --type-only $<

replay: listpub.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) -L $(THEORY_DIR) listpub

smoke: listpub.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) -L $(THEORY_DIR) listpub --smoke-detector top

.PHONY: clean
clean:
	rm -f prelistpub.mlw
	rm -f listpub.mlw
