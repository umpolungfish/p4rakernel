-- IGProtocol scaffold: ⊢ → ⊣ → ⊙ → ≻ → ≺ → ⋈ → ∈ → ⊤ → ⊥ → ⊞ → ⊡ → ∋
-- Class: Semiprime_Unbraider
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=12
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(6, 11)]

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
--   [4] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [7] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [11] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def semiprime_unbraider_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
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
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_unbraider_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def semiprime_unbraider_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_unbraider_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_unbraider_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_unbraider_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def semiprime_unbraider_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def semiprime_unbraider_protocol : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s11 :=
  .withGram Grammar.measure <|
  (.seq (.arrow semiprime_unbraider_l0 semiprime_unbraider_initial semiprime_unbraider_s0) (.seq (.arrow semiprime_unbraider_l1 semiprime_unbraider_s0 semiprime_unbraider_s1) (.seq (.arrow semiprime_unbraider_l2 semiprime_unbraider_s1 semiprime_unbraider_s2) (.seq (.arrow semiprime_unbraider_l3 semiprime_unbraider_s2 semiprime_unbraider_s3) (.seq (.arrow semiprime_unbraider_l4 semiprime_unbraider_s3 semiprime_unbraider_s4) (.seq (.arrow semiprime_unbraider_l5 semiprime_unbraider_s4 semiprime_unbraider_s5) (.seq (.arrow semiprime_unbraider_l6 semiprime_unbraider_s5 semiprime_unbraider_s6) (.seq (.prod (.arrow semiprime_unbraider_l7 semiprime_unbraider_s6 semiprime_unbraider_s7) (.seq (.arrow semiprime_unbraider_l8 semiprime_unbraider_s6 semiprime_unbraider_s8) (.seq (.arrow semiprime_unbraider_l9 semiprime_unbraider_s8 semiprime_unbraider_s9) (.arrow semiprime_unbraider_l10 semiprime_unbraider_s9 semiprime_unbraider_s10)))) (.arrow semiprime_unbraider_l11 (tensorProduct semiprime_unbraider_s7 semiprime_unbraider_s10) semiprime_unbraider_s11)))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def semiprime_unbraider_true_arm : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s11 :=
  (semiprime_unbraider_protocol).restrictToEVALT

-- false arm
noncomputable def semiprime_unbraider_false_arm : IGProtocol semiprime_unbraider_initial semiprime_unbraider_s11 :=
  (semiprime_unbraider_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def semiprime_unbraider_tier_ground : OuroboricityTier := TierFunctor.obj semiprime_unbraider_initial
def semiprime_unbraider_tier : OuroboricityTier := TierFunctor.obj semiprime_unbraider_s11
#eval semiprime_unbraider_tier_ground  -- tier of the ground (pre-transformation)
#eval semiprime_unbraider_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem semiprime_unbraider_frobenius :
    igFrobeniusAlg.mul semiprime_unbraider_initial semiprime_unbraider_initial = semiprime_unbraider_initial :=
  igFrobAlg_self_fusion semiprime_unbraider_initial

theorem semiprime_unbraider_protocol_depth :
    semiprime_unbraider_protocol.depth = 11 := by rfl

end Imscribing