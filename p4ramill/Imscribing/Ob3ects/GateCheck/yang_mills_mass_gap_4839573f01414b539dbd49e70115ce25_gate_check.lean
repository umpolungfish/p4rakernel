-- IGProtocol scaffold: ⊢ → ⊣ → ≻ → ≺ → ⋈ → ⊙ → ∈ → ⊥ → ⊤ → ⊞ → ∋ → ⊡ → ⋈ → ⋈ → ⊙ → ⋈ → ⊤ → ⊥ → ⊞ → ⊡ → ≻ → ≺ → ⋈ → ⊙
-- Class: Yang_Mills_Mass_Gap
-- Fingerprint: sig=(14,2,6,2)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=24
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(6, 10)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [2] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [6] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [7] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [8] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [14] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [15] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [19] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [20] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [21] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def yang_mills_mass_gap_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def yang_mills_mass_gap_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def yang_mills_mass_gap_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def yang_mills_mass_gap_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def yang_mills_mass_gap_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def yang_mills_mass_gap_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def yang_mills_mass_gap_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def yang_mills_mass_gap_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def yang_mills_mass_gap_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def yang_mills_mass_gap_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def yang_mills_mass_gap_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def yang_mills_mass_gap_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def yang_mills_mass_gap_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def yang_mills_mass_gap_l20 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def yang_mills_mass_gap_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def yang_mills_mass_gap_protocol : IGProtocol yang_mills_mass_gap_initial yang_mills_mass_gap_s23 :=
  .withGram Grammar.measure <|
  (.seq (.arrow yang_mills_mass_gap_l0 yang_mills_mass_gap_initial yang_mills_mass_gap_s0) (.seq (.arrow yang_mills_mass_gap_l1 yang_mills_mass_gap_s0 yang_mills_mass_gap_s1) (.seq (.arrow yang_mills_mass_gap_l2 yang_mills_mass_gap_s1 yang_mills_mass_gap_s2) (.seq (.arrow yang_mills_mass_gap_l3 yang_mills_mass_gap_s2 yang_mills_mass_gap_s3) (.seq (.arrow yang_mills_mass_gap_l4 yang_mills_mass_gap_s3 yang_mills_mass_gap_s4) (.seq (.arrow yang_mills_mass_gap_l5 yang_mills_mass_gap_s4 yang_mills_mass_gap_s5) (.seq (.arrow yang_mills_mass_gap_l6 yang_mills_mass_gap_s5 yang_mills_mass_gap_s6) (.seq (.prod (.seq (.arrow yang_mills_mass_gap_l8 yang_mills_mass_gap_s6 yang_mills_mass_gap_s8) (.arrow yang_mills_mass_gap_l9 yang_mills_mass_gap_s8 yang_mills_mass_gap_s9)) (.arrow yang_mills_mass_gap_l7 yang_mills_mass_gap_s6 yang_mills_mass_gap_s7)) (.seq (.arrow yang_mills_mass_gap_l10 (tensorProduct yang_mills_mass_gap_s9 yang_mills_mass_gap_s7) yang_mills_mass_gap_s10) (.seq (.arrow yang_mills_mass_gap_l11 yang_mills_mass_gap_s10 yang_mills_mass_gap_s11) (.seq (.arrow yang_mills_mass_gap_l12 yang_mills_mass_gap_s11 yang_mills_mass_gap_s12) (.seq (.arrow yang_mills_mass_gap_l13 yang_mills_mass_gap_s12 yang_mills_mass_gap_s13) (.seq (.arrow yang_mills_mass_gap_l14 yang_mills_mass_gap_s13 yang_mills_mass_gap_s14) (.seq (.arrow yang_mills_mass_gap_l15 yang_mills_mass_gap_s14 yang_mills_mass_gap_s15) (.seq (.arrow yang_mills_mass_gap_l16 yang_mills_mass_gap_s15 yang_mills_mass_gap_s16) (.seq (.arrow yang_mills_mass_gap_l17 yang_mills_mass_gap_s16 yang_mills_mass_gap_s17) (.seq (.arrow yang_mills_mass_gap_l18 yang_mills_mass_gap_s17 yang_mills_mass_gap_s18) (.seq (.arrow yang_mills_mass_gap_l19 yang_mills_mass_gap_s18 yang_mills_mass_gap_s19) (.seq (.arrow yang_mills_mass_gap_l20 yang_mills_mass_gap_s19 yang_mills_mass_gap_s20) (.seq (.arrow yang_mills_mass_gap_l21 yang_mills_mass_gap_s20 yang_mills_mass_gap_s21) (.seq (.arrow yang_mills_mass_gap_l22 yang_mills_mass_gap_s21 yang_mills_mass_gap_s22) (.arrow yang_mills_mass_gap_l23 yang_mills_mass_gap_s22 yang_mills_mass_gap_s23))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def yang_mills_mass_gap_true_arm : IGProtocol yang_mills_mass_gap_initial yang_mills_mass_gap_s23 :=
  (yang_mills_mass_gap_protocol).restrictToEVALT

-- false arm
noncomputable def yang_mills_mass_gap_false_arm : IGProtocol yang_mills_mass_gap_initial yang_mills_mass_gap_s23 :=
  (yang_mills_mass_gap_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def yang_mills_mass_gap_tier_ground : OuroboricityTier := TierFunctor.obj yang_mills_mass_gap_initial
def yang_mills_mass_gap_tier : OuroboricityTier := TierFunctor.obj yang_mills_mass_gap_s23
#eval yang_mills_mass_gap_tier_ground  -- tier of the ground (pre-transformation)
#eval yang_mills_mass_gap_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem yang_mills_mass_gap_frobenius :
    igFrobeniusAlg.mul yang_mills_mass_gap_initial yang_mills_mass_gap_initial = yang_mills_mass_gap_initial :=
  igFrobAlg_self_fusion yang_mills_mass_gap_initial

theorem yang_mills_mass_gap_protocol_depth :
    yang_mills_mass_gap_protocol.depth = 23 := by rfl

end Imscribing