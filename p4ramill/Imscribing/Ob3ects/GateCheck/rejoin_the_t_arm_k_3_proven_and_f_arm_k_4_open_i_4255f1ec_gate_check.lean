-- IGProtocol scaffold: VINIT → IMSCRIB → FSPLIT → AFWD → EVALT → CLINK → AREV → EVALF → ENGAGR → IFIX → FFUSE → TANCH
-- Class: Rejoin the T-arm (k=3 proven) and F-arm (k≥4 open) into a single dialetheic verdict, fusing the partial proof and the obstruction.
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
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_protocol : IGProtocol rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 = rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 (idempotent)
  (.seq (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s1) (.seq (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l1 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s1 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s2) (.seq (.prod (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l2 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s2 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10) (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l2 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s2 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10)) (.seq (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l10 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10) (.arrow rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_l10 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s10 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11)))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_true_arm : IGProtocol rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11 :=
  (rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_protocol).restrictToEVALT

-- false arm
noncomputable def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_false_arm : IGProtocol rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11 :=
  (rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_tier_ground : OuroboricityTier := TierFunctor.obj rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0
def rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_tier : OuroboricityTier := TierFunctor.obj rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s11
#eval rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_tier_ground  -- tier of the ground (pre-transformation)
#eval rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_frobenius :
    igFrobeniusAlg.mul rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 = rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0 :=
  igFrobAlg_self_fusion rejoin_the_t_arm_k_3_proven_and_f_arm_k_6ac8d3_s0
