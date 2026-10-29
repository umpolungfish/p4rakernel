-- IGProtocol scaffold: ⊢ → ≻ → ∈ → ⊤ → ⊥ → ⊞ → ∋ → ≺ → ⋈ → ⊙ → ⊡ → ⊣
-- Class: imasm_hotswaps
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
--   [4] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [5] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [6] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [11] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def imasm_hotswaps_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def imasm_hotswaps_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def imasm_hotswaps_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def imasm_hotswaps_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def imasm_hotswaps_protocol : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s11 :=
  .withGram Grammar.measure <|
  (.seq (.arrow imasm_hotswaps_l0 imasm_hotswaps_initial imasm_hotswaps_s0) (.seq (.arrow imasm_hotswaps_l1 imasm_hotswaps_s0 imasm_hotswaps_s1) (.seq (.arrow imasm_hotswaps_l2 imasm_hotswaps_s1 imasm_hotswaps_s2) (.seq (.prod (.arrow imasm_hotswaps_l3 imasm_hotswaps_s2 imasm_hotswaps_s3) (.seq (.arrow imasm_hotswaps_l4 imasm_hotswaps_s2 imasm_hotswaps_s4) (.arrow imasm_hotswaps_l5 imasm_hotswaps_s4 imasm_hotswaps_s5))) (.seq (.arrow imasm_hotswaps_l6 (tensorProduct imasm_hotswaps_s3 imasm_hotswaps_s5) imasm_hotswaps_s6) (.seq (.arrow imasm_hotswaps_l7 imasm_hotswaps_s6 imasm_hotswaps_s7) (.seq (.arrow imasm_hotswaps_l8 imasm_hotswaps_s7 imasm_hotswaps_s8) (.seq (.arrow imasm_hotswaps_l9 imasm_hotswaps_s8 imasm_hotswaps_s9) (.seq (.arrow imasm_hotswaps_l10 imasm_hotswaps_s9 imasm_hotswaps_s10) (.arrow imasm_hotswaps_l11 imasm_hotswaps_s10 imasm_hotswaps_s11))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def imasm_hotswaps_true_arm : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s11 :=
  (imasm_hotswaps_protocol).restrictToEVALT

-- false arm
noncomputable def imasm_hotswaps_false_arm : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s11 :=
  (imasm_hotswaps_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def imasm_hotswaps_tier_ground : OuroboricityTier := TierFunctor.obj imasm_hotswaps_initial
def imasm_hotswaps_tier : OuroboricityTier := TierFunctor.obj imasm_hotswaps_s11
#eval imasm_hotswaps_tier_ground  -- tier of the ground (pre-transformation)
#eval imasm_hotswaps_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem imasm_hotswaps_frobenius :
    igFrobeniusAlg.mul imasm_hotswaps_initial imasm_hotswaps_initial = imasm_hotswaps_initial :=
  igFrobAlg_self_fusion imasm_hotswaps_initial

theorem imasm_hotswaps_protocol_depth :
    imasm_hotswaps_protocol.depth = 11 := by rfl

end Imscribing