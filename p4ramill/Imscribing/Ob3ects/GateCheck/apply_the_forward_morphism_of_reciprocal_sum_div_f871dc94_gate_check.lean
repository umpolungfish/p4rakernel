-- IGProtocol scaffold: VINIT → AFWD → FSPLIT → EVALT → CLINK → EVALT → IFIX → AREV → EVALF → ENGAGR → CLINK → IMSCRIB → FFUSE → IFIX → TANCH
-- Class: Apply the forward morphism of reciprocal sum divergence to the set A.
-- Fingerprint: sig=(7,2,4,2)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=15
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(2, 12)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑾  | initial object — ground of distinction
--   [1] AFWD      rel    := 𐑾               𐑼 → 𐑚  | forward morphism — bidirectional arrow
--   [2] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [4] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [5] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [6] IFIX      prot   := 𐑭               𐑚 → 𐑙  | irreversible fixation — winding number
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [9] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [10] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [11] IMSCRIB   gram   := 𐑠               𐑚 → 𐑙  | identity — self-imscription
--   [12] FFUSE     stoi   := 𐑙               𐑙 → 𐑭  | fuse μ — assembly mode
--   [13] IFIX      prot   := 𐑭               𐑙 → 𐑡  | irreversible fixation — winding number
--   [14] TANCH     top    := 𐑡               𐑭 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def apply_the_forward_morphism_of_60a7ca_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def apply_the_forward_morphism_of_60a7ca_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def apply_the_forward_morphism_of_60a7ca_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def apply_the_forward_morphism_of_60a7ca_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def apply_the_forward_morphism_of_60a7ca_protocol : IGProtocol apply_the_forward_morphism_of_60a7ca_s0 apply_the_forward_morphism_of_60a7ca_s14 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct apply_the_forward_morphism_of_60a7ca_s12 apply_the_forward_morphism_of_60a7ca_s12 = apply_the_forward_morphism_of_60a7ca_s12 (idempotent)
  (.seq (.arrow apply_the_forward_morphism_of_60a7ca_l0 apply_the_forward_morphism_of_60a7ca_s0 apply_the_forward_morphism_of_60a7ca_s1) (.seq (.arrow apply_the_forward_morphism_of_60a7ca_l1 apply_the_forward_morphism_of_60a7ca_s1 apply_the_forward_morphism_of_60a7ca_s2) (.seq (.prod (.arrow apply_the_forward_morphism_of_60a7ca_l2 apply_the_forward_morphism_of_60a7ca_s2 apply_the_forward_morphism_of_60a7ca_s12) (.arrow apply_the_forward_morphism_of_60a7ca_l2 apply_the_forward_morphism_of_60a7ca_s2 apply_the_forward_morphism_of_60a7ca_s12)) (.seq (.arrow apply_the_forward_morphism_of_60a7ca_l12 apply_the_forward_morphism_of_60a7ca_s12 apply_the_forward_morphism_of_60a7ca_s12) (.seq (.arrow apply_the_forward_morphism_of_60a7ca_l12 apply_the_forward_morphism_of_60a7ca_s12 apply_the_forward_morphism_of_60a7ca_s13) (.arrow apply_the_forward_morphism_of_60a7ca_l13 apply_the_forward_morphism_of_60a7ca_s13 apply_the_forward_morphism_of_60a7ca_s14))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def apply_the_forward_morphism_of_60a7ca_true_arm : IGProtocol apply_the_forward_morphism_of_60a7ca_s0 apply_the_forward_morphism_of_60a7ca_s14 :=
  (apply_the_forward_morphism_of_60a7ca_protocol).restrictToEVALT

-- false arm
noncomputable def apply_the_forward_morphism_of_60a7ca_false_arm : IGProtocol apply_the_forward_morphism_of_60a7ca_s0 apply_the_forward_morphism_of_60a7ca_s14 :=
  (apply_the_forward_morphism_of_60a7ca_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def apply_the_forward_morphism_of_60a7ca_tier_ground : OuroboricityTier := TierFunctor.obj apply_the_forward_morphism_of_60a7ca_s0
def apply_the_forward_morphism_of_60a7ca_tier : OuroboricityTier := TierFunctor.obj apply_the_forward_morphism_of_60a7ca_s14
#eval apply_the_forward_morphism_of_60a7ca_tier_ground  -- tier of the ground (pre-transformation)
#eval apply_the_forward_morphism_of_60a7ca_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem apply_the_forward_morphism_of_60a7ca_frobenius :
    igFrobeniusAlg.mul apply_the_forward_morphism_of_60a7ca_s0 apply_the_forward_morphism_of_60a7ca_s0 = apply_the_forward_morphism_of_60a7ca_s0 :=
  igFrobAlg_self_fusion apply_the_forward_morphism_of_60a7ca_s0
