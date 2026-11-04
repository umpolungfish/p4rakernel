-- IGProtocol scaffold: ⊢ → ≻ → ∈ → ⊤ → ⋈ → ⊥ → ∋ → ⊙ → ≺ → ⊞ → ⊡ → ⊣
-- Class: Rules_of_Protein_folding
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=12
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 6)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [2] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [6] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [7] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [11] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def rules_of_protein_folding_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rules_of_protein_folding_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rules_of_protein_folding_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rules_of_protein_folding_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rules_of_protein_folding_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def rules_of_protein_folding_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def rules_of_protein_folding_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def rules_of_protein_folding_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rules_of_protein_folding_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rules_of_protein_folding_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rules_of_protein_folding_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def rules_of_protein_folding_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def rules_of_protein_folding_protocol : IGProtocol rules_of_protein_folding_initial rules_of_protein_folding_s11 :=
  .withGram Grammar.measure <|
  (.seq (.arrow rules_of_protein_folding_l0 rules_of_protein_folding_initial rules_of_protein_folding_s0) (.seq (.arrow rules_of_protein_folding_l1 rules_of_protein_folding_s0 rules_of_protein_folding_s1) (.seq (.arrow rules_of_protein_folding_l2 rules_of_protein_folding_s1 rules_of_protein_folding_s2) (.seq (.prod (.seq (.arrow rules_of_protein_folding_l3 rules_of_protein_folding_s2 rules_of_protein_folding_s3) (.arrow rules_of_protein_folding_l4 rules_of_protein_folding_s3 rules_of_protein_folding_s4)) (.arrow rules_of_protein_folding_l5 rules_of_protein_folding_s2 rules_of_protein_folding_s5)) (.seq (.arrow rules_of_protein_folding_l6 (tensorProduct rules_of_protein_folding_s4 rules_of_protein_folding_s5) rules_of_protein_folding_s6) (.seq (.arrow rules_of_protein_folding_l7 rules_of_protein_folding_s6 rules_of_protein_folding_s7) (.seq (.arrow rules_of_protein_folding_l8 rules_of_protein_folding_s7 rules_of_protein_folding_s8) (.seq (.arrow rules_of_protein_folding_l9 rules_of_protein_folding_s8 rules_of_protein_folding_s9) (.seq (.arrow rules_of_protein_folding_l10 rules_of_protein_folding_s9 rules_of_protein_folding_s10) (.arrow rules_of_protein_folding_l11 rules_of_protein_folding_s10 rules_of_protein_folding_s11))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def rules_of_protein_folding_true_arm : IGProtocol rules_of_protein_folding_initial rules_of_protein_folding_s11 :=
  (rules_of_protein_folding_protocol).restrictToEVALT

-- false arm
noncomputable def rules_of_protein_folding_false_arm : IGProtocol rules_of_protein_folding_initial rules_of_protein_folding_s11 :=
  (rules_of_protein_folding_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def rules_of_protein_folding_tier_ground : OuroboricityTier := TierFunctor.obj rules_of_protein_folding_initial
def rules_of_protein_folding_tier : OuroboricityTier := TierFunctor.obj rules_of_protein_folding_s11
#eval rules_of_protein_folding_tier_ground  -- tier of the ground (pre-transformation)
#eval rules_of_protein_folding_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem rules_of_protein_folding_frobenius :
    igFrobeniusAlg.mul rules_of_protein_folding_initial rules_of_protein_folding_initial = rules_of_protein_folding_initial :=
  igFrobAlg_self_fusion rules_of_protein_folding_initial

theorem rules_of_protein_folding_protocol_depth :
    rules_of_protein_folding_protocol.depth = 11 := by rfl

end Imscribing