import test from 'node:test';
import assert from 'node:assert/strict';
import {
  analyzeFixedPoints,
  buildOperatorTable,
  computeOrbit,
  evaluateCombinatorTokens,
  evaluateImasmWord,
  joinI,
  joinT,
  meetI,
  meetT,
  verifyCanonicalOracle,
} from './sixteen3';
import { auditBelnapTheorems } from './belnap';
import { evaluateImscriptionPair, IMSCRIPTION_PRESETS, getFineStructureBreakdown } from './imscribing';

test('SIXTEEN_3 trilattice matches bridge/check.py identities', () => {
  assert.equal(joinI(5, 10), 15);
  assert.equal(meetI(5, 10), 0);
  assert.equal(joinT(1, 2), 2);
  assert.equal(meetT(1, 2), 1);

  const orb = computeOrbit(buildOperatorTable('negation'), 2, '1000000000001');
  assert.equal(orb.period, 2);
  assert.equal(orb.value, 4);

  const rai = analyzeFixedPoints(buildOperatorTable('retain_after_inject', 7, 10));
  assert.equal(rai.leastFixedPoint, 2);
  assert.equal(rai.greatestFixedPoint, 7);

  const iar = analyzeFixedPoints(buildOperatorTable('inject_after_retain', 7, 10));
  assert.equal(iar.leastFixedPoint, 10);
  assert.equal(iar.greatestFixedPoint, 15);
});

test('SKIY combinator Y K K data:6 @ @ @ reduces to kernel-reentry 6', () => {
  const res = evaluateCombinatorTokens(['Y', 'K', 'K', 'data:6', '@', '@', '@']);
  assert.equal(res.valid, true);
  assert.equal(res.kernelReentry, 6);
  assert.equal(res.least, 6);
  assert.equal(res.greatest, 6);
  assert.equal(res.certified, true);
});

test('BankedWeight IMASM dichotomy holds for same-region, sibling-region, and premature-fuse', () => {
  assert.equal(evaluateImasmWord('∈⊤⊤≺∋').totalRecoveredWeight, 2);
  assert.equal(evaluateImasmWord('∈⊤∈⊤∋≺∋').totalRecoveredWeight, 1);
  assert.equal(evaluateImasmWord('∈⊤⊤∋≺∋').totalRecoveredWeight, 0);
});

test('Canonical Lean oracle 256 lattice rows match', () => {
  const oracle = verifyCanonicalOracle();
  assert.equal(oracle.passed, true);
});

test('Belnap FOUR Frobenius closure and cuts audit', () => {
  const audit = auditBelnapTheorems();
  assert.equal(audit.frobeniusClosureHolds, true);
  assert.equal(audit.theTwoCutsDifferAtN, true);
  assert.equal(audit.booleanCentreAdjunctionHolds, true);
});

test('Imscription Frobenius laws and fine-structure constant match', () => {
  const res = evaluateImscriptionPair(
    IMSCRIPTION_PRESETS.human_brain.tuple,
    IMSCRIPTION_PRESETS.replicative_core.tuple
  );
  assert.equal(res.frobeniusLaws.muDeltaA_id, true);
  assert.equal(res.frobeniusLaws.muDeltaB_id, true);
  assert.equal(res.frobeniusLaws.muDeltaD_id, true);
  assert.equal(res.consciousnessA.score, 1);

  const fsc = getFineStructureBreakdown();
  assert.equal(fsc.integerCore, 137);
  assert.ok(fsc.ppm < 0.01);
});
