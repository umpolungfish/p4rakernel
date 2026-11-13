-- IGProtocol scaffold: ⊢ → ⊣ → ≻ → ≺ → ⋈ → ⊙ → ∈ → ⊤ → ⊥ → ⊞ → ∋ → ⊡ → ⋈ → ⋈ → ≻ → ≺ → ⊤ → ⊥ → ⊞ → ⊡
-- Class: Semiprime_Unbraider
-- Fingerprint: sig=(10,2,6,2)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=20
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
--   [7] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [14] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [15] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [19] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def semiprime_unbraider_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def semiprime_unbraider_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def semiprime_unbraider_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def semiprime_unbraider_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_unbraider_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_unbraider_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def semiprime_unbraider_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_unbraider_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_unbraider_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def semiprime_unbraider_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_unbraider_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_unbraider_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def semiprime_unbraider_protocol : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s19 :=
  .withGram Grammar.measure <|
  (.seq (.arrow semiprime_unbraider_l0 semiprime_unbraider_initial semiprime_unbraider_s0) (.seq (.arrow semiprime_unbraider_l1 semiprime_unbraider_s0 semiprime_unbraider_s1) (.seq (.arrow semiprime_unbraider_l2 semiprime_unbraider_s1 semiprime_unbraider_s2) (.seq (.arrow semiprime_unbraider_l3 semiprime_unbraider_s2 semiprime_unbraider_s3) (.seq (.arrow semiprime_unbraider_l4 semiprime_unbraider_s3 semiprime_unbraider_s4) (.seq (.arrow semiprime_unbraider_l5 semiprime_unbraider_s4 semiprime_unbraider_s5) (.seq (.arrow semiprime_unbraider_l6 semiprime_unbraider_s5 semiprime_unbraider_s6) (.seq (.prod (.arrow semiprime_unbraider_l7 semiprime_unbraider_s6 semiprime_unbraider_s7) (.seq (.arrow semiprime_unbraider_l8 semiprime_unbraider_s6 semiprime_unbraider_s8) (.arrow semiprime_unbraider_l9 semiprime_unbraider_s8 semiprime_unbraider_s9))) (.seq (.arrow semiprime_unbraider_l10 (tensorProduct semiprime_unbraider_s7 semiprime_unbraider_s9) semiprime_unbraider_s10) (.seq (.arrow semiprime_unbraider_l11 semiprime_unbraider_s10 semiprime_unbraider_s11) (.seq (.arrow semiprime_unbraider_l12 semiprime_unbraider_s11 semiprime_unbraider_s12) (.seq (.arrow semiprime_unbraider_l13 semiprime_unbraider_s12 semiprime_unbraider_s13) (.seq (.arrow semiprime_unbraider_l14 semiprime_unbraider_s13 semiprime_unbraider_s14) (.seq (.arrow semiprime_unbraider_l15 semiprime_unbraider_s14 semiprime_unbraider_s15) (.seq (.arrow semiprime_unbraider_l16 semiprime_unbraider_s15 semiprime_unbraider_s16) (.seq (.arrow semiprime_unbraider_l17 semiprime_unbraider_s16 semiprime_unbraider_s17) (.seq (.arrow semiprime_unbraider_l18 semiprime_unbraider_s17 semiprime_unbraider_s18) (.arrow semiprime_unbraider_l19 semiprime_unbraider_s18 semiprime_unbraider_s19))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def semiprime_unbraider_true_arm : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s19 :=
  (semiprime_unbraider_protocol).restrictToEVALT

-- false arm
noncomputable def semiprime_unbraider_false_arm : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s19 :=
  (semiprime_unbraider_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def semiprime_unbraider_tier_ground : OuroboricityTier := TierFunctor.obj semiprime_unbraider_initial
def semiprime_unbraider_tier : OuroboricityTier := TierFunctor.obj semiprime_unbraider_s19
#eval semiprime_unbraider_tier_ground  -- tier of the ground (pre-transformation)
#eval semiprime_unbraider_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem semiprime_unbraider_frobenius :
    igFrobeniusAlg.mul semiprime_unbraider_initial semiprime_unbraider_initial = semiprime_unbraider_initial :=
  igFrobAlg_self_fusion semiprime_unbraider_initial

theorem semiprime_unbraider_protocol_depth :
    semiprime_unbraider_protocol.depth = 19 := by rfl

end Imscribing