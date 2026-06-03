# p4rakernel Makefile — Genetics test targets
# Usage: make test-<section>   or   make test-genetics (all)

PYTHON := python3
TEST_RUNNER := ./test_genetics.py

.PHONY: test-genetics test-b4 test-codons test-tuples test-pipeline \
        test-phi test-kernel test-consistency test-quick help

test-genetics:
	$(PYTHON) $(TEST_RUNNER)

test-b4:
	$(PYTHON) $(TEST_RUNNER) --b4

test-codons:
	$(PYTHON) $(TEST_RUNNER) --codons

test-tuples:
	$(PYTHON) $(TEST_RUNNER) --tuples

test-pipeline:
	$(PYTHON) $(TEST_RUNNER) --pipeline

test-phi:
	$(PYTHON) $(TEST_RUNNER) --phi

test-kernel:
	$(PYTHON) $(TEST_RUNNER) --kernel

test-consistency:
	$(PYTHON) $(TEST_RUNNER) --consistency

test-quick:
	$(PYTHON) $(TEST_RUNNER) --quick

help:
	@echo "p4rakernel genetics test targets:"
	@echo "  make test-genetics      — run ALL genetics tests"
	@echo "  make test-b4            — B4 nucleotide lattice"
	@echo "  make test-codons        — 64-codon Frobenius verification"
	@echo "  make test-tuples        — 7-stage tuple generation"
	@echo "  make test-pipeline      — gene→protein pipeline smoke"
	@echo "  make test-phi           — phi=odot three-condition gate"
	@echo "  make test-kernel        — ParaASM kernel Frobenius"
	@echo "  make test-consistency   — cross-file His->odot / Gln->Gamma"
	@echo "  make test-quick         — b4 + codons + pipeline only"
