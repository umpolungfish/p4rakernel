-- IGProtocol scaffold: ⊢ → ≻ → ⋈ → ⊙ → ∈ → ⊤ → ⊥ → ⊞ → ∋ → ≺ → ⊣ → ⊡ → ⋈ → ⋈
-- Class: anyon_braid_protein_folding_operator
-- Fingerprint: sig=(8,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=14
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 8)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [2] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [3] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [4] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [7] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [8] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [9] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [10] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def anyon_braid_protein_folding_operator_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def anyon_braid_protein_folding_operator_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def anyon_braid_protein_folding_operator_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def anyon_braid_protein_folding_operator_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def anyon_braid_protein_folding_operator_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def anyon_braid_protein_folding_operator_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def anyon_braid_protein_folding_operator_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def anyon_braid_protein_folding_operator_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def anyon_braid_protein_folding_operator_protocol : IGProtocol anyon_braid_protein_folding_operator_initial anyon_braid_protein_folding_operator_s13 :=
  .withGram Grammar.measure <|
  (.seq (.arrow anyon_braid_protein_folding_operator_l0 anyon_braid_protein_folding_operator_initial anyon_braid_protein_folding_operator_s0) (.seq (.arrow anyon_braid_protein_folding_operator_l1 anyon_braid_protein_folding_operator_s0 anyon_braid_protein_folding_operator_s1) (.seq (.arrow anyon_braid_protein_folding_operator_l2 anyon_braid_protein_folding_operator_s1 anyon_braid_protein_folding_operator_s2) (.seq (.arrow anyon_braid_protein_folding_operator_l3 anyon_braid_protein_folding_operator_s2 anyon_braid_protein_folding_operator_s3) (.seq (.arrow anyon_braid_protein_folding_operator_l4 anyon_braid_protein_folding_operator_s3 anyon_braid_protein_folding_operator_s4) (.seq (.prod (.arrow anyon_braid_protein_folding_operator_l5 anyon_braid_protein_folding_operator_s4 anyon_braid_protein_folding_operator_s5) (.seq (.arrow anyon_braid_protein_folding_operator_l6 anyon_braid_protein_folding_operator_s4 anyon_braid_protein_folding_operator_s6) (.arrow anyon_braid_protein_folding_operator_l7 anyon_braid_protein_folding_operator_s6 anyon_braid_protein_folding_operator_s7))) (.seq (.arrow anyon_braid_protein_folding_operator_l8 (tensorProduct anyon_braid_protein_folding_operator_s5 anyon_braid_protein_folding_operator_s7) anyon_braid_protein_folding_operator_s8) (.seq (.arrow anyon_braid_protein_folding_operator_l9 anyon_braid_protein_folding_operator_s8 anyon_braid_protein_folding_operator_s9) (.seq (.arrow anyon_braid_protein_folding_operator_l10 anyon_braid_protein_folding_operator_s9 anyon_braid_protein_folding_operator_s10) (.seq (.arrow anyon_braid_protein_folding_operator_l11 anyon_braid_protein_folding_operator_s10 anyon_braid_protein_folding_operator_s11) (.seq (.arrow anyon_braid_protein_folding_operator_l12 anyon_braid_protein_folding_operator_s11 anyon_braid_protein_folding_operator_s12) (.arrow anyon_braid_protein_folding_operator_l13 anyon_braid_protein_folding_operator_s12 anyon_braid_protein_folding_operator_s13))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def anyon_braid_protein_folding_operator_true_arm : IGProtocol anyon_braid_protein_folding_operator_initial anyon_braid_protein_folding_operator_s13 :=
  (anyon_braid_protein_folding_operator_protocol).restrictToEVALT

-- false arm
noncomputable def anyon_braid_protein_folding_operator_false_arm : IGProtocol anyon_braid_protein_folding_operator_initial anyon_braid_protein_folding_operator_s13 :=
  (anyon_braid_protein_folding_operator_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def anyon_braid_protein_folding_operator_tier_ground : OuroboricityTier := TierFunctor.obj anyon_braid_protein_folding_operator_initial
def anyon_braid_protein_folding_operator_tier : OuroboricityTier := TierFunctor.obj anyon_braid_protein_folding_operator_s13
#eval anyon_braid_protein_folding_operator_tier_ground  -- tier of the ground (pre-transformation)
#eval anyon_braid_protein_folding_operator_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem anyon_braid_protein_folding_operator_frobenius :
    igFrobeniusAlg.mul anyon_braid_protein_folding_operator_initial anyon_braid_protein_folding_operator_initial = anyon_braid_protein_folding_operator_initial :=
  igFrobAlg_self_fusion anyon_braid_protein_folding_operator_initial

theorem anyon_braid_protein_folding_operator_protocol_depth :
    anyon_braid_protein_folding_operator_protocol.depth = 13 := by rfl

end Imscribing