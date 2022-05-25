WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed

all: tiling.mlw

tiling.mlw: tiling.rl
	$(WHYREL) -margin 136 -o $@ $^
	sed -f $(POST_PROCESS) -i $@

ide: tiling.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f tiling.mlw
