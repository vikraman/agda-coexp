AGDA_SRCS = $(shell find -H Coexp -type f -name '*.agda')
AGDA_BINS = $(subst .agda,.agdai,$(AGDA_SRCS))

all: Coexp/Everything.agdai
reallyall: $(AGDA_BINS)

%.agdai: %.agda
	agda $<

html: index.agda $(AGDA_SRCS)
	agda --html index.agda

todos: $(AGDA_SRCS)
	find -H Coexp -type f -name '*.agda' \
		-exec grep -E -n --colour=auto 'TODO' {} \+

cloc:
	cloc Coexp/

clean:
	rm -f $(AGDA_BINS)

.PHONY: all clean
