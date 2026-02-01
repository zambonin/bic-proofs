LAKE ?= $(or $(wildcard $(HOME)/.elan/bin/lake),lake)
SRC = GenericRankingBic.lean $(wildcard GenericRankingBic/*/*.lean) \
	$(wildcard ProofAudit/*.lean)
TARGETS = $(addprefix +,$(subst /,.,$(SRC:.lean=)))

all:
	$(LAKE) build

check:
	$(LAKE) --no-cache --rehash build $(TARGETS)
	$(LAKE) env lean ProofAudit/AllAxioms.lean

comparator: check
	$(LAKE) env comparator ProofAudit/comparator.json

clean:
	$(LAKE) clean GenericRankingBic

.PHONY: all check comparator clean
