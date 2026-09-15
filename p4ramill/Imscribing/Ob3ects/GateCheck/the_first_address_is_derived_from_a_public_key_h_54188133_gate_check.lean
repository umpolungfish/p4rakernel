-- IGProtocol scaffold: VINIT → AFWD → CLINK → FSPLIT → EVALT → IMSCRIB → TANCH → AREV → EVALF → ENGAGR → FFUSE → IFIX
-- Class: the first address is derived from a public key hash, establishing self-identity
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=12
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
--   [5] IMSCRIB   gram   := 𐑠               𐑚 → 𐑙  | identity — self-imscription
--   [6] TANCH     top    := 𐑡               𐑚 → 𐑙  | terminal object — connectivity boundary
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [9] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑭  | fuse μ — assembly mode
--   [11] IFIX      prot   := 𐑭               𐑙 → 𐑼  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_first_address_is_derived_from_a_d90899_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_first_address_is_derived_from_a_d90899_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_first_address_is_derived_from_a_d90899_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_first_address_is_derived_from_a_d90899_protocol : IGProtocol the_first_address_is_derived_from_a_d90899_s0 the_first_address_is_derived_from_a_d90899_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct the_first_address_is_derived_from_a_d90899_s10 the_first_address_is_derived_from_a_d90899_s10 = the_first_address_is_derived_from_a_d90899_s10 (idempotent)
  (.seq (.arrow the_first_address_is_derived_from_a_d90899_l0 the_first_address_is_derived_from_a_d90899_s0 the_first_address_is_derived_from_a_d90899_s1) (.seq (.arrow the_first_address_is_derived_from_a_d90899_l1 the_first_address_is_derived_from_a_d90899_s1 the_first_address_is_derived_from_a_d90899_s2) (.seq (.arrow the_first_address_is_derived_from_a_d90899_l2 the_first_address_is_derived_from_a_d90899_s2 the_first_address_is_derived_from_a_d90899_s3) (.seq (.prod (.arrow the_first_address_is_derived_from_a_d90899_l3 the_first_address_is_derived_from_a_d90899_s3 the_first_address_is_derived_from_a_d90899_s10) (.arrow the_first_address_is_derived_from_a_d90899_l3 the_first_address_is_derived_from_a_d90899_s3 the_first_address_is_derived_from_a_d90899_s10)) (.seq (.arrow the_first_address_is_derived_from_a_d90899_l10 the_first_address_is_derived_from_a_d90899_s10 the_first_address_is_derived_from_a_d90899_s10) (.arrow the_first_address_is_derived_from_a_d90899_l10 the_first_address_is_derived_from_a_d90899_s10 the_first_address_is_derived_from_a_d90899_s11))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_first_address_is_derived_from_a_d90899_true_arm : IGProtocol the_first_address_is_derived_from_a_d90899_s0 the_first_address_is_derived_from_a_d90899_s11 :=
  (the_first_address_is_derived_from_a_d90899_protocol).restrictToEVALT

-- false arm
noncomputable def the_first_address_is_derived_from_a_d90899_false_arm : IGProtocol the_first_address_is_derived_from_a_d90899_s0 the_first_address_is_derived_from_a_d90899_s11 :=
  (the_first_address_is_derived_from_a_d90899_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_first_address_is_derived_from_a_d90899_tier_ground : OuroboricityTier := TierFunctor.obj the_first_address_is_derived_from_a_d90899_s0
def the_first_address_is_derived_from_a_d90899_tier : OuroboricityTier := TierFunctor.obj the_first_address_is_derived_from_a_d90899_s11
#eval the_first_address_is_derived_from_a_d90899_tier_ground  -- tier of the ground (pre-transformation)
#eval the_first_address_is_derived_from_a_d90899_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem the_first_address_is_derived_from_a_d90899_frobenius :
    igFrobeniusAlg.mul the_first_address_is_derived_from_a_d90899_s0 the_first_address_is_derived_from_a_d90899_s0 = the_first_address_is_derived_from_a_d90899_s0 :=
  igFrobAlg_self_fusion the_first_address_is_derived_from_a_d90899_s0
