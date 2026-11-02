-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ⋈ → ≻ → ⊥ → ≺ → ∋ → ⊞ → ⊡ → ⊣ → ⊙
-- Class: Peptide_Folding_Operator
-- Fingerprint: sig=(7,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=13
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 8)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [6] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [11] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [12] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def peptide_folding_operator_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def peptide_folding_operator_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def peptide_folding_operator_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def peptide_folding_operator_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def peptide_folding_operator_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def peptide_folding_operator_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def peptide_folding_operator_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def peptide_folding_operator_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def peptide_folding_operator_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def peptide_folding_operator_protocol : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s12 :=
  .withGram Grammar.measure <|
  (.seq (.arrow peptide_folding_operator_l0 peptide_folding_operator_initial peptide_folding_operator_s0) (.seq (.arrow peptide_folding_operator_l1 peptide_folding_operator_s0 peptide_folding_operator_s1) (.seq (.arrow peptide_folding_operator_l2 peptide_folding_operator_s1 peptide_folding_operator_s2) (.seq (.prod (.seq (.arrow peptide_folding_operator_l3 peptide_folding_operator_s2 peptide_folding_operator_s3) (.seq (.arrow peptide_folding_operator_l4 peptide_folding_operator_s3 peptide_folding_operator_s4) (.arrow peptide_folding_operator_l5 peptide_folding_operator_s4 peptide_folding_operator_s5))) (.seq (.arrow peptide_folding_operator_l6 peptide_folding_operator_s2 peptide_folding_operator_s6) (.arrow peptide_folding_operator_l7 peptide_folding_operator_s6 peptide_folding_operator_s7))) (.seq (.arrow peptide_folding_operator_l8 (tensorProduct peptide_folding_operator_s5 peptide_folding_operator_s7) peptide_folding_operator_s8) (.seq (.arrow peptide_folding_operator_l9 peptide_folding_operator_s8 peptide_folding_operator_s9) (.seq (.arrow peptide_folding_operator_l10 peptide_folding_operator_s9 peptide_folding_operator_s10) (.seq (.arrow peptide_folding_operator_l11 peptide_folding_operator_s10 peptide_folding_operator_s11) (.arrow peptide_folding_operator_l12 peptide_folding_operator_s11 peptide_folding_operator_s12)))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def peptide_folding_operator_true_arm : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s12 :=
  (peptide_folding_operator_protocol).restrictToEVALT

-- false arm
noncomputable def peptide_folding_operator_false_arm : IGProtocol peptide_folding_operator_initial peptide_folding_operator_s12 :=
  (peptide_folding_operator_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def peptide_folding_operator_tier_ground : OuroboricityTier := TierFunctor.obj peptide_folding_operator_initial
def peptide_folding_operator_tier : OuroboricityTier := TierFunctor.obj peptide_folding_operator_s12
#eval peptide_folding_operator_tier_ground  -- tier of the ground (pre-transformation)
#eval peptide_folding_operator_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem peptide_folding_operator_frobenius :
    igFrobeniusAlg.mul peptide_folding_operator_initial peptide_folding_operator_initial = peptide_folding_operator_initial :=
  igFrobAlg_self_fusion peptide_folding_operator_initial

theorem peptide_folding_operator_protocol_depth :
    peptide_folding_operator_protocol.depth = 11 := by rfl

end Imscribing