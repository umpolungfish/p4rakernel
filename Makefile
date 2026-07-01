# p4rakernel Makefile — Genetics test targets
# Usage: make test-<section>   or   make test-genetics (all)

PYTHON := python3
TEST_RUNNER := ./test_genetics.py

# Canonical toolchain for the loose top-level Lean files is the paraconsistent
# kernel fork (this repo's src/, v4.28.0), built to build/stage1/bin.
LEAN := ./build/stage1/bin/lean

.PHONY: test-genetics test-b4 test-codons test-tuples test-pipeline \
        test-phi test-kernel test-consistency test-quick help lean-oleans

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

# Rebuild the loose top-level oleans (gitignored) under the fork, in dependency
# order. Regenerates the shared imports so the standalone Lean files load without
# a stock/fork version mismatch.
lean-oleans:
	$(LEAN) ParaconsistentCore.lean -o ParaconsistentCore.olean
	LEAN_PATH=. $(LEAN) ParaconsistentFrobeniusClosure.lean -o ParaconsistentFrobeniusClosure.olean
	LEAN_PATH=. $(LEAN) ClassicalRestriction.lean -o ClassicalRestriction.olean
	@echo "Built top-level oleans under the paraconsistent fork ($(LEAN))."

help:
	@echo "p4rakernel genetics test targets:"
	@echo "  make lean-oleans        — rebuild loose top-level oleans under the fork"
	@echo "  make test-genetics      — run ALL genetics tests"
	@echo "  make test-b4            — B4 nucleotide lattice"
	@echo "  make test-codons        — 64-codon Frobenius verification"
	@echo "  make test-tuples        — 7-stage tuple generation"
	@echo "  make test-pipeline      — gene→protein pipeline smoke"
	@echo "  make test-phi           — phi=odot three-condition gate"
	@echo "  make test-kernel        — ParaASM kernel Frobenius"
	@echo "  make test-consistency   — cross-file His->odot / Gln->Gamma"
	@echo "  make test-quick         — b4 + codons + pipeline only"
