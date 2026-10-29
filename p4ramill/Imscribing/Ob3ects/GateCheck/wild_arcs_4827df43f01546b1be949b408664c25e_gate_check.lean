-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ≻ → ⋈ → ⊙ → ∈ → ⊤ → ≻ → ⊙ → ⊥ → ≺ → ⊙ → ∋ → ⊞ → ⊤ → ∈ → ∋ → ⊙ → ⊥ → ≻ → ⋈ → ⊡ → ⊡ → ⊙ → ⊣
-- Class: Wild_Arcs
-- Fingerprint: sig=(16,4,5,2)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=27
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(7, 14), (17, 18)]

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
--   [4] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [8] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [9] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [12] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [13] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [14] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [15] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [18] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [19] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [20] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [21] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [24] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [25] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [26] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def wild_arcs_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def wild_arcs_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def wild_arcs_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def wild_arcs_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def wild_arcs_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def wild_arcs_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def wild_arcs_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def wild_arcs_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l9 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def wild_arcs_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def wild_arcs_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def wild_arcs_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def wild_arcs_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def wild_arcs_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def wild_arcs_protocol : IGProtocol wild_arcs_initial wild_arcs_s26 :=
  .withGram Grammar.measure <|
  (.seq (.arrow wild_arcs_l0 wild_arcs_initial wild_arcs_s0) (.seq (.arrow wild_arcs_l1 wild_arcs_s0 wild_arcs_s1) (.seq (.arrow wild_arcs_l2 wild_arcs_s1 wild_arcs_s2) (.seq (.arrow wild_arcs_l3 wild_arcs_s2 wild_arcs_s3) (.seq (.arrow wild_arcs_l4 wild_arcs_s3 wild_arcs_s4) (.seq (.arrow wild_arcs_l5 wild_arcs_s4 wild_arcs_s5) (.seq (.arrow wild_arcs_l6 wild_arcs_s5 wild_arcs_s6) (.seq (.arrow wild_arcs_l7 wild_arcs_s6 wild_arcs_s7) (.seq (.prod (.seq (.arrow wild_arcs_l8 wild_arcs_s7 wild_arcs_s8) (.seq (.arrow wild_arcs_l9 wild_arcs_s8 wild_arcs_s9) (.arrow wild_arcs_l10 wild_arcs_s9 wild_arcs_s10))) (.seq (.arrow wild_arcs_l11 wild_arcs_s7 wild_arcs_s11) (.seq (.arrow wild_arcs_l12 wild_arcs_s11 wild_arcs_s12) (.arrow wild_arcs_l13 wild_arcs_s12 wild_arcs_s13)))) (.seq (.arrow wild_arcs_l14 (tensorProduct wild_arcs_s10 wild_arcs_s13) wild_arcs_s14) (.seq (.arrow wild_arcs_l15 wild_arcs_s14 wild_arcs_s15) (.seq (.arrow wild_arcs_l16 wild_arcs_s15 wild_arcs_s16) (.seq (.arrow wild_arcs_l17 wild_arcs_s16 wild_arcs_s17) (.seq (.prod (.refl wild_arcs_s17) (.refl wild_arcs_s17)) (.seq (.arrow wild_arcs_l18 (tensorProduct wild_arcs_s17 wild_arcs_s17) wild_arcs_s18) (.seq (.arrow wild_arcs_l19 wild_arcs_s18 wild_arcs_s19) (.seq (.arrow wild_arcs_l20 wild_arcs_s19 wild_arcs_s20) (.seq (.arrow wild_arcs_l21 wild_arcs_s20 wild_arcs_s21) (.seq (.arrow wild_arcs_l22 wild_arcs_s21 wild_arcs_s22) (.seq (.arrow wild_arcs_l23 wild_arcs_s22 wild_arcs_s23) (.seq (.arrow wild_arcs_l24 wild_arcs_s23 wild_arcs_s24) (.seq (.arrow wild_arcs_l25 wild_arcs_s24 wild_arcs_s25) (.arrow wild_arcs_l26 wild_arcs_s25 wild_arcs_s26)))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def wild_arcs_true_arm : IGProtocol wild_arcs_initial wild_arcs_s26 :=
  (wild_arcs_protocol).restrictToEVALT

-- false arm
noncomputable def wild_arcs_false_arm : IGProtocol wild_arcs_initial wild_arcs_s26 :=
  (wild_arcs_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def wild_arcs_tier_ground : OuroboricityTier := TierFunctor.obj wild_arcs_initial
def wild_arcs_tier : OuroboricityTier := TierFunctor.obj wild_arcs_s26
#eval wild_arcs_tier_ground  -- tier of the ground (pre-transformation)
#eval wild_arcs_tier  -- the Grammar's tuple-tier verdict

theorem wild_arcs_protocol_depth :
    wild_arcs_protocol.depth = 24 := by rfl

end Imscribing