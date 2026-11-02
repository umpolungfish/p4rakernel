-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊙ → ≻ → ∈ → ⊥ → ≺ → ⊤ → ∋ → ⋈ → ⊞ → ∈ → ⊤ → ⊥ → ∋ → ⊣ → ⊡ → ⊙ → ≺ → ⋈ → ⊡
-- Class: Protein_Folding_Operator
-- Fingerprint: sig=(12,5,6,2)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=25
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(8, 12), (15, 18)]

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
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [8] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [10] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [13] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [14] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [15] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [19] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [20] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [21] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [22] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def protein_folding_operator_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def protein_folding_operator_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def protein_folding_operator_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def protein_folding_operator_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def protein_folding_operator_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def protein_folding_operator_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def protein_folding_operator_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def protein_folding_operator_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def protein_folding_operator_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def protein_folding_operator_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def protein_folding_operator_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def protein_folding_operator_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def protein_folding_operator_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def protein_folding_operator_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def protein_folding_operator_protocol : IGProtocol protein_folding_operator_initial protein_folding_operator_s24 :=
  .withGram Grammar.measure <|
  (.seq (.arrow protein_folding_operator_l0 protein_folding_operator_initial protein_folding_operator_s0) (.seq (.arrow protein_folding_operator_l1 protein_folding_operator_s0 protein_folding_operator_s1) (.seq (.arrow protein_folding_operator_l2 protein_folding_operator_s1 protein_folding_operator_s2) (.seq (.arrow protein_folding_operator_l3 protein_folding_operator_s2 protein_folding_operator_s3) (.seq (.arrow protein_folding_operator_l4 protein_folding_operator_s3 protein_folding_operator_s4) (.seq (.arrow protein_folding_operator_l5 protein_folding_operator_s4 protein_folding_operator_s5) (.seq (.arrow protein_folding_operator_l6 protein_folding_operator_s5 protein_folding_operator_s6) (.seq (.arrow protein_folding_operator_l7 protein_folding_operator_s6 protein_folding_operator_s7) (.seq (.arrow protein_folding_operator_l8 protein_folding_operator_s7 protein_folding_operator_s8) (.seq (.prod (.arrow protein_folding_operator_l11 protein_folding_operator_s8 protein_folding_operator_s11) (.seq (.arrow protein_folding_operator_l9 protein_folding_operator_s8 protein_folding_operator_s9) (.arrow protein_folding_operator_l10 protein_folding_operator_s9 protein_folding_operator_s10))) (.seq (.arrow protein_folding_operator_l12 (tensorProduct protein_folding_operator_s11 protein_folding_operator_s10) protein_folding_operator_s12) (.seq (.arrow protein_folding_operator_l13 protein_folding_operator_s12 protein_folding_operator_s13) (.seq (.arrow protein_folding_operator_l14 protein_folding_operator_s13 protein_folding_operator_s14) (.seq (.arrow protein_folding_operator_l15 protein_folding_operator_s14 protein_folding_operator_s15) (.seq (.prod (.arrow protein_folding_operator_l16 protein_folding_operator_s15 protein_folding_operator_s16) (.arrow protein_folding_operator_l17 protein_folding_operator_s15 protein_folding_operator_s17)) (.seq (.arrow protein_folding_operator_l18 (tensorProduct protein_folding_operator_s16 protein_folding_operator_s17) protein_folding_operator_s18) (.seq (.arrow protein_folding_operator_l19 protein_folding_operator_s18 protein_folding_operator_s19) (.seq (.arrow protein_folding_operator_l20 protein_folding_operator_s19 protein_folding_operator_s20) (.seq (.arrow protein_folding_operator_l21 protein_folding_operator_s20 protein_folding_operator_s21) (.seq (.arrow protein_folding_operator_l22 protein_folding_operator_s21 protein_folding_operator_s22) (.seq (.arrow protein_folding_operator_l23 protein_folding_operator_s22 protein_folding_operator_s23) (.arrow protein_folding_operator_l24 protein_folding_operator_s23 protein_folding_operator_s24))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def protein_folding_operator_true_arm : IGProtocol protein_folding_operator_initial protein_folding_operator_s24 :=
  (protein_folding_operator_protocol).restrictToEVALT

-- false arm
noncomputable def protein_folding_operator_false_arm : IGProtocol protein_folding_operator_initial protein_folding_operator_s24 :=
  (protein_folding_operator_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def protein_folding_operator_tier_ground : OuroboricityTier := TierFunctor.obj protein_folding_operator_initial
def protein_folding_operator_tier : OuroboricityTier := TierFunctor.obj protein_folding_operator_s24
#eval protein_folding_operator_tier_ground  -- tier of the ground (pre-transformation)
#eval protein_folding_operator_tier  -- the Grammar's tuple-tier verdict

theorem protein_folding_operator_protocol_depth :
    protein_folding_operator_protocol.depth = 23 := by rfl

end Imscribing