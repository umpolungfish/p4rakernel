-- IGProtocol scaffold: ⊢ → ⊣ → ≻ → ⋈ → ≻ → ⋈ → ⊙ → ∈ → ⊤ → ⊥ → ⊞ → ∋ → ≺ → ⊡ → ⊣
-- Class: gematriatic_factor_extraction
-- Fingerprint: sig=(9,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=15
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(7, 11)]

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
--   [3] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [8] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [9] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [10] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [11] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [12] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [13] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [14] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def gematriatic_factor_extraction_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def gematriatic_factor_extraction_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def gematriatic_factor_extraction_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def gematriatic_factor_extraction_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def gematriatic_factor_extraction_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def gematriatic_factor_extraction_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def gematriatic_factor_extraction_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def gematriatic_factor_extraction_protocol : IGProtocol gematriatic_factor_extraction_initial gematriatic_factor_extraction_s14 :=
  .withGram Grammar.measure <|
  (.seq (.arrow gematriatic_factor_extraction_l0 gematriatic_factor_extraction_initial gematriatic_factor_extraction_s0) (.seq (.arrow gematriatic_factor_extraction_l1 gematriatic_factor_extraction_s0 gematriatic_factor_extraction_s1) (.seq (.arrow gematriatic_factor_extraction_l2 gematriatic_factor_extraction_s1 gematriatic_factor_extraction_s2) (.seq (.arrow gematriatic_factor_extraction_l3 gematriatic_factor_extraction_s2 gematriatic_factor_extraction_s3) (.seq (.arrow gematriatic_factor_extraction_l4 gematriatic_factor_extraction_s3 gematriatic_factor_extraction_s4) (.seq (.arrow gematriatic_factor_extraction_l5 gematriatic_factor_extraction_s4 gematriatic_factor_extraction_s5) (.seq (.arrow gematriatic_factor_extraction_l6 gematriatic_factor_extraction_s5 gematriatic_factor_extraction_s6) (.seq (.arrow gematriatic_factor_extraction_l7 gematriatic_factor_extraction_s6 gematriatic_factor_extraction_s7) (.seq (.prod (.arrow gematriatic_factor_extraction_l8 gematriatic_factor_extraction_s7 gematriatic_factor_extraction_s8) (.seq (.arrow gematriatic_factor_extraction_l9 gematriatic_factor_extraction_s7 gematriatic_factor_extraction_s9) (.arrow gematriatic_factor_extraction_l10 gematriatic_factor_extraction_s9 gematriatic_factor_extraction_s10))) (.seq (.arrow gematriatic_factor_extraction_l11 (tensorProduct gematriatic_factor_extraction_s8 gematriatic_factor_extraction_s10) gematriatic_factor_extraction_s11) (.seq (.arrow gematriatic_factor_extraction_l12 gematriatic_factor_extraction_s11 gematriatic_factor_extraction_s12) (.seq (.arrow gematriatic_factor_extraction_l13 gematriatic_factor_extraction_s12 gematriatic_factor_extraction_s13) (.arrow gematriatic_factor_extraction_l14 gematriatic_factor_extraction_s13 gematriatic_factor_extraction_s14)))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def gematriatic_factor_extraction_true_arm : IGProtocol gematriatic_factor_extraction_initial gematriatic_factor_extraction_s14 :=
  (gematriatic_factor_extraction_protocol).restrictToEVALT

-- false arm
noncomputable def gematriatic_factor_extraction_false_arm : IGProtocol gematriatic_factor_extraction_initial gematriatic_factor_extraction_s14 :=
  (gematriatic_factor_extraction_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def gematriatic_factor_extraction_tier_ground : OuroboricityTier := TierFunctor.obj gematriatic_factor_extraction_initial
def gematriatic_factor_extraction_tier : OuroboricityTier := TierFunctor.obj gematriatic_factor_extraction_s14
#eval gematriatic_factor_extraction_tier_ground  -- tier of the ground (pre-transformation)
#eval gematriatic_factor_extraction_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem gematriatic_factor_extraction_frobenius :
    igFrobeniusAlg.mul gematriatic_factor_extraction_initial gematriatic_factor_extraction_initial = gematriatic_factor_extraction_initial :=
  igFrobAlg_self_fusion gematriatic_factor_extraction_initial

theorem gematriatic_factor_extraction_protocol_depth :
    gematriatic_factor_extraction_protocol.depth = 14 := by rfl

end Imscribing