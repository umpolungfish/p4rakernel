-- IGProtocol scaffold: VINIT → AFWD → CLINK → FSPLIT → EVALT → AFWD → EVALF → AREV → ENGAGR → CLINK → FFUSE → IFIX → IMSCRIB → TANCH
-- Class: the structure of a problem that forks and does not rejoin
-- Fingerprint: sig=(8,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=14
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(3, 10)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑾  | initial object — ground of distinction
--   [1] AFWD      rel    := 𐑾               𐑼 → 𐑱  | forward morphism — bidirectional arrow
--   [2] CLINK     fid    := 𐑱               𐑾 → 𐑚  | composition — regime coherence
--   [3] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [5] AFWD      rel    := 𐑾               𐑚 → 𐑙  | forward morphism — bidirectional arrow
--   [6] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [9] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑭  | fuse μ — assembly mode
--   [11] IFIX      prot   := 𐑭               𐑙 → 𐑠  | irreversible fixation — winding number
--   [12] IMSCRIB   gram   := 𐑠               𐑭 → 𐑡  | identity — self-imscription
--   [13] TANCH     top    := 𐑡               𐑠 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_structure_of_a_problem_that_forks_303eee_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_structure_of_a_problem_that_forks_303eee_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_structure_of_a_problem_that_forks_303eee_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_structure_of_a_problem_that_forks_303eee_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_structure_of_a_problem_that_forks_303eee_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_structure_of_a_problem_that_forks_303eee_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_structure_of_a_problem_that_forks_303eee_protocol : IGProtocol the_structure_of_a_problem_that_forks_303eee_s0 the_structure_of_a_problem_that_forks_303eee_s13 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_structure_of_a_problem_that_forks_303eee_s10 the_structure_of_a_problem_that_forks_303eee_s10 = the_structure_of_a_problem_that_forks_303eee_s10 (idempotent)
  (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l0 the_structure_of_a_problem_that_forks_303eee_s0 the_structure_of_a_problem_that_forks_303eee_s1) (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l1 the_structure_of_a_problem_that_forks_303eee_s1 the_structure_of_a_problem_that_forks_303eee_s2) (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l2 the_structure_of_a_problem_that_forks_303eee_s2 the_structure_of_a_problem_that_forks_303eee_s3) (.seq (.prod (.arrow the_structure_of_a_problem_that_forks_303eee_l3 the_structure_of_a_problem_that_forks_303eee_s3 the_structure_of_a_problem_that_forks_303eee_s10) (.arrow the_structure_of_a_problem_that_forks_303eee_l3 the_structure_of_a_problem_that_forks_303eee_s3 the_structure_of_a_problem_that_forks_303eee_s10)) (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l10 the_structure_of_a_problem_that_forks_303eee_s10 the_structure_of_a_problem_that_forks_303eee_s10) (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l10 the_structure_of_a_problem_that_forks_303eee_s10 the_structure_of_a_problem_that_forks_303eee_s11) (.seq (.arrow the_structure_of_a_problem_that_forks_303eee_l11 the_structure_of_a_problem_that_forks_303eee_s11 the_structure_of_a_problem_that_forks_303eee_s12) (.arrow the_structure_of_a_problem_that_forks_303eee_l12 the_structure_of_a_problem_that_forks_303eee_s12 the_structure_of_a_problem_that_forks_303eee_s13))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_structure_of_a_problem_that_forks_303eee_true_arm : IGProtocol the_structure_of_a_problem_that_forks_303eee_s0 the_structure_of_a_problem_that_forks_303eee_s13 :=
  (the_structure_of_a_problem_that_forks_303eee_protocol).restrictToEVALT

-- false arm
noncomputable def the_structure_of_a_problem_that_forks_303eee_false_arm : IGProtocol the_structure_of_a_problem_that_forks_303eee_s0 the_structure_of_a_problem_that_forks_303eee_s13 :=
  (the_structure_of_a_problem_that_forks_303eee_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_structure_of_a_problem_that_forks_303eee_tier_ground : OuroboricityTier := TierFunctor.obj the_structure_of_a_problem_that_forks_303eee_s0
def the_structure_of_a_problem_that_forks_303eee_tier : OuroboricityTier := TierFunctor.obj the_structure_of_a_problem_that_forks_303eee_s13
#eval the_structure_of_a_problem_that_forks_303eee_tier_ground  -- tier of the ground (pre-transformation)
#eval the_structure_of_a_problem_that_forks_303eee_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem the_structure_of_a_problem_that_forks_303eee_frobenius :
    igFrobeniusAlg.mul the_structure_of_a_problem_that_forks_303eee_s0 the_structure_of_a_problem_that_forks_303eee_s0 = the_structure_of_a_problem_that_forks_303eee_s0 :=
  igFrobAlg_self_fusion the_structure_of_a_problem_that_forks_303eee_s0
