-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊥ → ⊞ → ≺ → ⋈ → ⊤ → ∈ → ∋ → ∋ → ⊡ → ⊙ → ⊣
-- Class: bottom_quark
-- Fingerprint: sig=(8,4,4,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=17
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(11, 12), (3, 13)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [7] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [10] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [11] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [12] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [15] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [16] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def bottom_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def bottom_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def bottom_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def bottom_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def bottom_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def bottom_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def bottom_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def bottom_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def bottom_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def bottom_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def bottom_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def bottom_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def bottom_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def bottom_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def bottom_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def bottom_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def bottom_quark_protocol : IGProtocol bottom_quark_initial bottom_quark_s16 :=
  .withGram Grammar.measure <|
  (.seq (.arrow bottom_quark_l0 bottom_quark_initial bottom_quark_s0) (.seq (.arrow bottom_quark_l1 bottom_quark_s0 bottom_quark_s1) (.seq (.arrow bottom_quark_l2 bottom_quark_s1 bottom_quark_s2) (.seq (.arrow bottom_quark_l3 bottom_quark_s2 bottom_quark_s3) (.seq (.prod (.seq (.arrow bottom_quark_l4 bottom_quark_s3 bottom_quark_s4) (.arrow bottom_quark_l5 bottom_quark_s4 bottom_quark_s5)) (.seq (.arrow bottom_quark_l6 bottom_quark_s3 bottom_quark_s6) (.seq (.arrow bottom_quark_l7 bottom_quark_s6 bottom_quark_s7) (.seq (.arrow bottom_quark_l8 bottom_quark_s7 bottom_quark_s8) (.seq (.arrow bottom_quark_l9 bottom_quark_s8 bottom_quark_s9) (.seq (.arrow bottom_quark_l10 bottom_quark_s9 bottom_quark_s10) (.seq (.arrow bottom_quark_l11 bottom_quark_s10 bottom_quark_s11) (.seq (.prod (.refl bottom_quark_s11) (.refl bottom_quark_s11)) (.arrow bottom_quark_l12 (tensorProduct bottom_quark_s11 bottom_quark_s11) bottom_quark_s12))))))))) (.seq (.arrow bottom_quark_l13 (tensorProduct bottom_quark_s5 bottom_quark_s12) bottom_quark_s13) (.seq (.arrow bottom_quark_l14 bottom_quark_s13 bottom_quark_s14) (.seq (.arrow bottom_quark_l15 bottom_quark_s14 bottom_quark_s15) (.arrow bottom_quark_l16 bottom_quark_s15 bottom_quark_s16)))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def bottom_quark_true_arm : IGProtocol bottom_quark_initial bottom_quark_s16 :=
  (bottom_quark_protocol).restrictToEVALT

-- false arm
noncomputable def bottom_quark_false_arm : IGProtocol bottom_quark_initial bottom_quark_s16 :=
  (bottom_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def bottom_quark_tier_ground : OuroboricityTier := TierFunctor.obj bottom_quark_initial
def bottom_quark_tier : OuroboricityTier := TierFunctor.obj bottom_quark_s16
#eval bottom_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval bottom_quark_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem bottom_quark_frobenius :
    igFrobeniusAlg.mul bottom_quark_initial bottom_quark_initial = bottom_quark_initial :=
  igFrobAlg_self_fusion bottom_quark_initial

theorem bottom_quark_protocol_depth :
    bottom_quark_protocol.depth = 15 := by rfl

end Imscribing