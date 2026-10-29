-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ⊙ → ∈ → ⊤ → ≻ → ∈ → ⊤ → ⊥ → ∋ → ⊥ → ∋ → ≺ → ⋈ → ⊙ → ⊡ → ⊣
-- Class: top_quark
-- Fingerprint: sig=(10,4,4,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=19
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(8, 11), (5, 13)]

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
--   [3] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [5] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [6] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [7] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [8] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [10] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [11] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [12] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [15] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [16] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [17] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [18] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def top_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def top_quark_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def top_quark_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def top_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def top_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def top_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def top_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def top_quark_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def top_quark_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def top_quark_protocol : IGProtocol top_quark_initial top_quark_s18 :=
  .withGram Grammar.measure <|
  (.seq (.arrow top_quark_l0 top_quark_initial top_quark_s0) (.seq (.arrow top_quark_l1 top_quark_s0 top_quark_s1) (.seq (.arrow top_quark_l2 top_quark_s1 top_quark_s2) (.seq (.arrow top_quark_l3 top_quark_s2 top_quark_s3) (.seq (.arrow top_quark_l4 top_quark_s3 top_quark_s4) (.seq (.arrow top_quark_l5 top_quark_s4 top_quark_s5) (.seq (.prod (.seq (.arrow top_quark_l6 top_quark_s5 top_quark_s6) (.seq (.arrow top_quark_l7 top_quark_s6 top_quark_s7) (.seq (.arrow top_quark_l8 top_quark_s7 top_quark_s8) (.seq (.prod (.arrow top_quark_l9 top_quark_s8 top_quark_s9) (.arrow top_quark_l10 top_quark_s8 top_quark_s10)) (.arrow top_quark_l11 (tensorProduct top_quark_s9 top_quark_s10) top_quark_s11))))) (.arrow top_quark_l12 top_quark_s5 top_quark_s12)) (.seq (.arrow top_quark_l13 (tensorProduct top_quark_s11 top_quark_s12) top_quark_s13) (.seq (.arrow top_quark_l14 top_quark_s13 top_quark_s14) (.seq (.arrow top_quark_l15 top_quark_s14 top_quark_s15) (.seq (.arrow top_quark_l16 top_quark_s15 top_quark_s16) (.seq (.arrow top_quark_l17 top_quark_s16 top_quark_s17) (.arrow top_quark_l18 top_quark_s17 top_quark_s18)))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def top_quark_true_arm : IGProtocol top_quark_initial top_quark_s18 :=
  (top_quark_protocol).restrictToEVALT

-- false arm
noncomputable def top_quark_false_arm : IGProtocol top_quark_initial top_quark_s18 :=
  (top_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def top_quark_tier_ground : OuroboricityTier := TierFunctor.obj top_quark_initial
def top_quark_tier : OuroboricityTier := TierFunctor.obj top_quark_s18
#eval top_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval top_quark_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem top_quark_frobenius :
    igFrobeniusAlg.mul top_quark_initial top_quark_initial = top_quark_initial :=
  igFrobAlg_self_fusion top_quark_initial

theorem top_quark_protocol_depth :
    top_quark_protocol.depth = 17 := by rfl

end Imscribing