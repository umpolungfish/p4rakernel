-- IGProtocol scaffold: VINIT → IMSCRIB → FSPLIT → AFWD → EVALT → CLINK → AREV → EVALF → ENGAGR → IFIX → FFUSE → TANCH
-- Class: On the T-arm, apply the forward morphism of the density bridge to convert reciprocal divergence into positive density.
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=12
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(2, 10)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑠  | initial object — ground of distinction
--   [1] IMSCRIB   gram   := 𐑠               𐑼 → 𐑚  | identity — self-imscription
--   [2] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] AFWD      rel    := 𐑾               𐑚 → 𐑙  | forward morphism — bidirectional arrow
--   [4] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [5] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [6] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [7] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [8] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [9] IFIX      prot   := 𐑭               𐑚 → 𐑙  | irreversible fixation — winding number
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑡  | fuse μ — assembly mode
--   [11] TANCH     top    := 𐑡               𐑙 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def on_the_t_arm_apply_the_forward_morphism_dd67b6_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def on_the_t_arm_apply_the_forward_morphism_dd67b6_protocol : IGProtocol on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 = on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 (idempotent)
  (.seq (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s1) (.seq (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l1 on_the_t_arm_apply_the_forward_morphism_dd67b6_s1 on_the_t_arm_apply_the_forward_morphism_dd67b6_s2) (.seq (.prod (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l2 on_the_t_arm_apply_the_forward_morphism_dd67b6_s2 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10) (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l2 on_the_t_arm_apply_the_forward_morphism_dd67b6_s2 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10)) (.seq (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l10 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10) (.arrow on_the_t_arm_apply_the_forward_morphism_dd67b6_l10 on_the_t_arm_apply_the_forward_morphism_dd67b6_s10 on_the_t_arm_apply_the_forward_morphism_dd67b6_s11)))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def on_the_t_arm_apply_the_forward_morphism_dd67b6_true_arm : IGProtocol on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s11 :=
  (on_the_t_arm_apply_the_forward_morphism_dd67b6_protocol).restrictToEVALT

-- false arm
noncomputable def on_the_t_arm_apply_the_forward_morphism_dd67b6_false_arm : IGProtocol on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s11 :=
  (on_the_t_arm_apply_the_forward_morphism_dd67b6_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def on_the_t_arm_apply_the_forward_morphism_dd67b6_tier_ground : OuroboricityTier := TierFunctor.obj on_the_t_arm_apply_the_forward_morphism_dd67b6_s0
def on_the_t_arm_apply_the_forward_morphism_dd67b6_tier : OuroboricityTier := TierFunctor.obj on_the_t_arm_apply_the_forward_morphism_dd67b6_s11
#eval on_the_t_arm_apply_the_forward_morphism_dd67b6_tier_ground  -- tier of the ground (pre-transformation)
#eval on_the_t_arm_apply_the_forward_morphism_dd67b6_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem on_the_t_arm_apply_the_forward_morphism_dd67b6_frobenius :
    igFrobeniusAlg.mul on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 = on_the_t_arm_apply_the_forward_morphism_dd67b6_s0 :=
  igFrobAlg_self_fusion on_the_t_arm_apply_the_forward_morphism_dd67b6_s0
