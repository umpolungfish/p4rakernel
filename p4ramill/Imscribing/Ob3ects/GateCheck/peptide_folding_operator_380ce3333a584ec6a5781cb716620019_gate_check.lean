-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ≻ → ⊥ → ≺ → ∋ → ⋈ → ⊞ → ≻ → ∈ → ⊤ → ⊥ → ∋ → ⊙ → ⊡ → ⊣
-- Class: Peptide_Folding_Operator
-- Fingerprint: sig=(10,4,5,1)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=20
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(3, 9), (13, 16)]

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
--   [6] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [7] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [10] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [11] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [12] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [13] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [14] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [15] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [16] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [17] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [18] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [19] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def peptide_folding_operator_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def peptide_folding_operator_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def peptide_folding_operator_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def peptide_folding_operator_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def peptide_folding_operator_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def peptide_folding_operator_protocol : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s19 :=
  .withGram Grammar.measure <|
  (.seq (.arrow peptide_folding_operator_l0 peptide_folding_operator_initial peptide_folding_operator_s0) (.seq (.arrow peptide_folding_operator_l1 peptide_folding_operator_s0 peptide_folding_operator_s1) (.seq (.arrow peptide_folding_operator_l2 peptide_folding_operator_s1 peptide_folding_operator_s2) (.seq (.arrow peptide_folding_operator_l3 peptide_folding_operator_s2 peptide_folding_operator_s3) (.seq (.prod (.seq (.arrow peptide_folding_operator_l4 peptide_folding_operator_s3 peptide_folding_operator_s4) (.seq (.arrow peptide_folding_operator_l5 peptide_folding_operator_s4 peptide_folding_operator_s5) (.arrow peptide_folding_operator_l6 peptide_folding_operator_s5 peptide_folding_operator_s6))) (.seq (.arrow peptide_folding_operator_l7 peptide_folding_operator_s3 peptide_folding_operator_s7) (.arrow peptide_folding_operator_l8 peptide_folding_operator_s7 peptide_folding_operator_s8))) (.seq (.arrow peptide_folding_operator_l9 (tensorProduct peptide_folding_operator_s6 peptide_folding_operator_s8) peptide_folding_operator_s9) (.seq (.arrow peptide_folding_operator_l10 peptide_folding_operator_s9 peptide_folding_operator_s10) (.seq (.arrow peptide_folding_operator_l11 peptide_folding_operator_s10 peptide_folding_operator_s11) (.seq (.arrow peptide_folding_operator_l12 peptide_folding_operator_s11 peptide_folding_operator_s12) (.seq (.arrow peptide_folding_operator_l13 peptide_folding_operator_s12 peptide_folding_operator_s13) (.seq (.prod (.arrow peptide_folding_operator_l14 peptide_folding_operator_s13 peptide_folding_operator_s14) (.arrow peptide_folding_operator_l15 peptide_folding_operator_s13 peptide_folding_operator_s15)) (.seq (.arrow peptide_folding_operator_l16 (tensorProduct peptide_folding_operator_s14 peptide_folding_operator_s15) peptide_folding_operator_s16) (.seq (.arrow peptide_folding_operator_l17 peptide_folding_operator_s16 peptide_folding_operator_s17) (.seq (.arrow peptide_folding_operator_l18 peptide_folding_operator_s17 peptide_folding_operator_s18) (.arrow peptide_folding_operator_l19 peptide_folding_operator_s18 peptide_folding_operator_s19)))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def peptide_folding_operator_true_arm : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s19 :=
  (peptide_folding_operator_protocol).restrictToEVALT

-- false arm
noncomputable def peptide_folding_operator_false_arm : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s19 :=
  (peptide_folding_operator_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def peptide_folding_operator_tier_ground : OuroboricityTier := TierFunctor.obj peptide_folding_operator_initial
def peptide_folding_operator_tier : OuroboricityTier := TierFunctor.obj peptide_folding_operator_s19
#eval peptide_folding_operator_tier_ground  -- tier of the ground (pre-transformation)
#eval peptide_folding_operator_tier  -- the Grammar's tuple-tier verdict

theorem peptide_folding_operator_protocol_depth :
    peptide_folding_operator_protocol.depth = 17 := by rfl

end Imscribing