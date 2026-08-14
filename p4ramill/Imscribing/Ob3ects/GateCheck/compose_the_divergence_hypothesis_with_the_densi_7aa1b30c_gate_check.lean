-- IGProtocol scaffold: VINIT → AFWD → FSPLIT → EVALT → CLINK → EVALT → IFIX → AREV → EVALF → ENGAGR → CLINK → IMSCRIB → FFUSE → IFIX → TANCH
-- Class: Compose the divergence hypothesis with the density bridge axiom to establish positive density.
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
private def compose_the_divergence_hypothesis_with_fc077e_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def compose_the_divergence_hypothesis_with_fc077e_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compose_the_divergence_hypothesis_with_fc077e_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def compose_the_divergence_hypothesis_with_fc077e_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def compose_the_divergence_hypothesis_with_fc077e_protocol : IGProtocol compose_the_divergence_hypothesis_with_fc077e_s0 compose_the_divergence_hypothesis_with_fc077e_s14 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct compose_the_divergence_hypothesis_with_fc077e_s12 compose_the_divergence_hypothesis_with_fc077e_s12 = compose_the_divergence_hypothesis_with_fc077e_s12 (idempotent)
  (.seq (.arrow compose_the_divergence_hypothesis_with_fc077e_l0 compose_the_divergence_hypothesis_with_fc077e_s0 compose_the_divergence_hypothesis_with_fc077e_s1) (.seq (.arrow compose_the_divergence_hypothesis_with_fc077e_l1 compose_the_divergence_hypothesis_with_fc077e_s1 compose_the_divergence_hypothesis_with_fc077e_s2) (.seq (.prod (.arrow compose_the_divergence_hypothesis_with_fc077e_l2 compose_the_divergence_hypothesis_with_fc077e_s2 compose_the_divergence_hypothesis_with_fc077e_s12) (.arrow compose_the_divergence_hypothesis_with_fc077e_l2 compose_the_divergence_hypothesis_with_fc077e_s2 compose_the_divergence_hypothesis_with_fc077e_s12)) (.seq (.arrow compose_the_divergence_hypothesis_with_fc077e_l12 compose_the_divergence_hypothesis_with_fc077e_s12 compose_the_divergence_hypothesis_with_fc077e_s12) (.seq (.arrow compose_the_divergence_hypothesis_with_fc077e_l12 compose_the_divergence_hypothesis_with_fc077e_s12 compose_the_divergence_hypothesis_with_fc077e_s13) (.arrow compose_the_divergence_hypothesis_with_fc077e_l13 compose_the_divergence_hypothesis_with_fc077e_s13 compose_the_divergence_hypothesis_with_fc077e_s14))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def compose_the_divergence_hypothesis_with_fc077e_true_arm : IGProtocol compose_the_divergence_hypothesis_with_fc077e_s0 compose_the_divergence_hypothesis_with_fc077e_s14 :=
  (compose_the_divergence_hypothesis_with_fc077e_protocol).restrictToEVALT

-- false arm
noncomputable def compose_the_divergence_hypothesis_with_fc077e_false_arm : IGProtocol compose_the_divergence_hypothesis_with_fc077e_s0 compose_the_divergence_hypothesis_with_fc077e_s14 :=
  (compose_the_divergence_hypothesis_with_fc077e_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def compose_the_divergence_hypothesis_with_fc077e_tier_ground : OuroboricityTier := TierFunctor.obj compose_the_divergence_hypothesis_with_fc077e_s0
def compose_the_divergence_hypothesis_with_fc077e_tier : OuroboricityTier := TierFunctor.obj compose_the_divergence_hypothesis_with_fc077e_s14
#eval compose_the_divergence_hypothesis_with_fc077e_tier_ground  -- tier of the ground (pre-transformation)
#eval compose_the_divergence_hypothesis_with_fc077e_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem compose_the_divergence_hypothesis_with_fc077e_frobenius :
    igFrobeniusAlg.mul compose_the_divergence_hypothesis_with_fc077e_s0 compose_the_divergence_hypothesis_with_fc077e_s0 = compose_the_divergence_hypothesis_with_fc077e_s0 :=
  igFrobAlg_self_fusion compose_the_divergence_hypothesis_with_fc077e_s0
