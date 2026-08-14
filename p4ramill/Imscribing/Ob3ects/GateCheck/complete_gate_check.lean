-- IGProtocol scaffold: VINIT → FSPLIT → FFUSE → EVALT → EVALF → ENGAGR → IFIX
-- Class: complete
-- Fingerprint: sig=(1,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=7
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(1, 2)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑚  | initial object — ground of distinction
--   [1] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [2] FFUSE     stoi   := 𐑙               𐑙 → ⊙  | fuse μ — assembly mode
--   [3] EVALT     crit   := ⊙               𐑙 → 𐑖  | evaluate-true — criticality gate open
--   [4] EVALF     chir   := 𐑖               ⊙ → 𐑳  | evaluate-false — chirality check
--   [5] ENGAGR    stoi   := 𐑳               𐑖 → 𐑭  | engage paradox — B-state, both arms
--   [6] IFIX      prot   := 𐑭               𐑳 → 𐑼  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def complete_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def complete_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def complete_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def complete_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def complete_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def complete_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def complete_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def complete_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def complete_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def complete_protocol : IGProtocol complete_s0 complete_s6 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct complete_s2 complete_s2 = complete_s2 (idempotent)
  (.seq (.arrow complete_l0 complete_s0 complete_s1) (.seq (.prod (.arrow complete_l1 complete_s1 complete_s2) (.arrow complete_l1 complete_s1 complete_s2)) (.seq (.arrow complete_l2 complete_s2 complete_s2) (.seq (.arrow complete_l2 complete_s2 complete_s3) (.seq (.arrow complete_l3 complete_s3 complete_s4) (.seq (.arrow complete_l4 complete_s4 complete_s5) (.arrow complete_l5 complete_s5 complete_s6)))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def complete_true_arm : IGProtocol complete_s0 complete_s6 :=
  (complete_protocol).restrictToEVALT

-- false arm
noncomputable def complete_false_arm : IGProtocol complete_s0 complete_s6 :=
  (complete_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def complete_tier_ground : OuroboricityTier := TierFunctor.obj complete_s0
def complete_tier : OuroboricityTier := TierFunctor.obj complete_s6
#eval complete_tier_ground  -- tier of the ground (pre-transformation)
#eval complete_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem complete_frobenius :
    igFrobeniusAlg.mul complete_s0 complete_s0 = complete_s0 :=
  igFrobAlg_self_fusion complete_s0
