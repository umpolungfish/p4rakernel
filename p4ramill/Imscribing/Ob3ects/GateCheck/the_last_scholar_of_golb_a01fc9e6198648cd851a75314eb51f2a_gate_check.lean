-- IGProtocol scaffold: ⊢ → ⊣ → ⊙ → ≻ → ∈ → ⊤ → ⊥ → ∋ → ⊞ → ⊡ → ⋈ → ≺ → ⋈ → ⊣
-- Class: The_Last_Scholar_of_Golb
-- Fingerprint: sig=(8,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=14
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 7)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [2] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [3] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [4] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [7] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [8] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [9] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [10] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [11] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_last_scholar_of_golb_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_last_scholar_of_golb_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_last_scholar_of_golb_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_last_scholar_of_golb_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_last_scholar_of_golb_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_last_scholar_of_golb_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_last_scholar_of_golb_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_last_scholar_of_golb_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_last_scholar_of_golb_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_last_scholar_of_golb_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_last_scholar_of_golb_protocol : IGProtocol the_last_scholar_of_golb_initial the_last_scholar_of_golb_s13 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_last_scholar_of_golb_l0 the_last_scholar_of_golb_initial the_last_scholar_of_golb_s0) (.seq (.arrow the_last_scholar_of_golb_l1 the_last_scholar_of_golb_s0 the_last_scholar_of_golb_s1) (.seq (.arrow the_last_scholar_of_golb_l2 the_last_scholar_of_golb_s1 the_last_scholar_of_golb_s2) (.seq (.arrow the_last_scholar_of_golb_l3 the_last_scholar_of_golb_s2 the_last_scholar_of_golb_s3) (.seq (.arrow the_last_scholar_of_golb_l4 the_last_scholar_of_golb_s3 the_last_scholar_of_golb_s4) (.seq (.prod (.arrow the_last_scholar_of_golb_l5 the_last_scholar_of_golb_s4 the_last_scholar_of_golb_s5) (.arrow the_last_scholar_of_golb_l6 the_last_scholar_of_golb_s4 the_last_scholar_of_golb_s6)) (.seq (.arrow the_last_scholar_of_golb_l7 (tensorProduct the_last_scholar_of_golb_s5 the_last_scholar_of_golb_s6) the_last_scholar_of_golb_s7) (.seq (.arrow the_last_scholar_of_golb_l8 the_last_scholar_of_golb_s7 the_last_scholar_of_golb_s8) (.seq (.arrow the_last_scholar_of_golb_l9 the_last_scholar_of_golb_s8 the_last_scholar_of_golb_s9) (.seq (.arrow the_last_scholar_of_golb_l10 the_last_scholar_of_golb_s9 the_last_scholar_of_golb_s10) (.seq (.arrow the_last_scholar_of_golb_l11 the_last_scholar_of_golb_s10 the_last_scholar_of_golb_s11) (.seq (.arrow the_last_scholar_of_golb_l12 the_last_scholar_of_golb_s11 the_last_scholar_of_golb_s12) (.arrow the_last_scholar_of_golb_l13 the_last_scholar_of_golb_s12 the_last_scholar_of_golb_s13)))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_last_scholar_of_golb_true_arm : IGProtocol the_last_scholar_of_golb_initial the_last_scholar_of_golb_s13 :=
  (the_last_scholar_of_golb_protocol).restrictToEVALT

-- false arm
noncomputable def the_last_scholar_of_golb_false_arm : IGProtocol the_last_scholar_of_golb_initial the_last_scholar_of_golb_s13 :=
  (the_last_scholar_of_golb_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_last_scholar_of_golb_tier_ground : OuroboricityTier := TierFunctor.obj the_last_scholar_of_golb_initial
def the_last_scholar_of_golb_tier : OuroboricityTier := TierFunctor.obj the_last_scholar_of_golb_s13
#eval the_last_scholar_of_golb_tier_ground  -- tier of the ground (pre-transformation)
#eval the_last_scholar_of_golb_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem the_last_scholar_of_golb_frobenius :
    igFrobeniusAlg.mul the_last_scholar_of_golb_initial the_last_scholar_of_golb_initial = the_last_scholar_of_golb_initial :=
  igFrobAlg_self_fusion the_last_scholar_of_golb_initial

theorem the_last_scholar_of_golb_protocol_depth :
    the_last_scholar_of_golb_protocol.depth = 13 := by rfl

end Imscribing