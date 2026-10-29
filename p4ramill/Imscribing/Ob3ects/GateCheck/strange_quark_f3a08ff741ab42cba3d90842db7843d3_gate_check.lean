-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊙ → ⋈ → ∈ → ⊤ → ⋈ → ⊥ → ⋈ → ∋ → ⊥ → ≻ → ≺ → ⋈ → ⊞ → ∋ → ⊡ → ⊣
-- Class: strange_quark
-- Fingerprint: sig=(12,4,5,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=22
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(8, 13), (3, 19)]

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
--   [3] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [8] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [10] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [11] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [15] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [18] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [19] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [20] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [21] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def strange_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def strange_quark_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def strange_quark_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def strange_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def strange_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def strange_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def strange_quark_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def strange_quark_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def strange_quark_protocol : IGProtocol strange_quark_initial strange_quark_s21 :=
  .withGram Grammar.measure <|
  (.seq (.arrow strange_quark_l0 strange_quark_initial strange_quark_s0) (.seq (.arrow strange_quark_l1 strange_quark_s0 strange_quark_s1) (.seq (.arrow strange_quark_l2 strange_quark_s1 strange_quark_s2) (.seq (.arrow strange_quark_l3 strange_quark_s2 strange_quark_s3) (.seq (.prod (.seq (.arrow strange_quark_l4 strange_quark_s3 strange_quark_s4) (.seq (.arrow strange_quark_l5 strange_quark_s4 strange_quark_s5) (.seq (.arrow strange_quark_l6 strange_quark_s5 strange_quark_s6) (.seq (.arrow strange_quark_l7 strange_quark_s6 strange_quark_s7) (.seq (.arrow strange_quark_l8 strange_quark_s7 strange_quark_s8) (.seq (.prod (.seq (.arrow strange_quark_l9 strange_quark_s8 strange_quark_s9) (.arrow strange_quark_l10 strange_quark_s9 strange_quark_s10)) (.seq (.arrow strange_quark_l11 strange_quark_s8 strange_quark_s11) (.arrow strange_quark_l12 strange_quark_s11 strange_quark_s12))) (.arrow strange_quark_l13 (tensorProduct strange_quark_s10 strange_quark_s12) strange_quark_s13))))))) (.seq (.arrow strange_quark_l14 strange_quark_s3 strange_quark_s14) (.seq (.arrow strange_quark_l15 strange_quark_s14 strange_quark_s15) (.seq (.arrow strange_quark_l16 strange_quark_s15 strange_quark_s16) (.seq (.arrow strange_quark_l17 strange_quark_s16 strange_quark_s17) (.arrow strange_quark_l18 strange_quark_s17 strange_quark_s18)))))) (.seq (.arrow strange_quark_l19 (tensorProduct strange_quark_s13 strange_quark_s18) strange_quark_s19) (.seq (.arrow strange_quark_l20 strange_quark_s19 strange_quark_s20) (.arrow strange_quark_l21 strange_quark_s20 strange_quark_s21))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def strange_quark_true_arm : IGProtocol strange_quark_initial strange_quark_s21 :=
  (strange_quark_protocol).restrictToEVALT

-- false arm
noncomputable def strange_quark_false_arm : IGProtocol strange_quark_initial strange_quark_s21 :=
  (strange_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def strange_quark_tier_ground : OuroboricityTier := TierFunctor.obj strange_quark_initial
def strange_quark_tier : OuroboricityTier := TierFunctor.obj strange_quark_s21
#eval strange_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval strange_quark_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem strange_quark_frobenius :
    igFrobeniusAlg.mul strange_quark_initial strange_quark_initial = strange_quark_initial :=
  igFrobAlg_self_fusion strange_quark_initial

theorem strange_quark_protocol_depth :
    strange_quark_protocol.depth = 15 := by rfl

end Imscribing