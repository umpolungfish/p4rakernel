-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊙ → ⊥ → ≻ → ≺ → ⋈ → ⊞ → ∋ → ⊡ → ⊣
-- Class: strange_quark
-- Fingerprint: sig=(9,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=15
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(3, 12)]

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
--   [7] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [8] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [9] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [10] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [11] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [12] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [13] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [14] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

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
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def strange_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def strange_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def strange_quark_s14 : Imscription :=
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
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def strange_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def strange_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def strange_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def strange_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def strange_quark_protocol : IGProtocol strange_quark_initial strange_quark_s14 :=
  .withGram Grammar.measure <|
  (.seq (.arrow strange_quark_l0 strange_quark_initial strange_quark_s0) (.seq (.arrow strange_quark_l1 strange_quark_s0 strange_quark_s1) (.seq (.arrow strange_quark_l2 strange_quark_s1 strange_quark_s2) (.seq (.arrow strange_quark_l3 strange_quark_s2 strange_quark_s3) (.seq (.prod (.seq (.arrow strange_quark_l4 strange_quark_s3 strange_quark_s4) (.seq (.arrow strange_quark_l5 strange_quark_s4 strange_quark_s5) (.arrow strange_quark_l6 strange_quark_s5 strange_quark_s6))) (.seq (.arrow strange_quark_l7 strange_quark_s3 strange_quark_s7) (.seq (.arrow strange_quark_l8 strange_quark_s7 strange_quark_s8) (.seq (.arrow strange_quark_l9 strange_quark_s8 strange_quark_s9) (.seq (.arrow strange_quark_l10 strange_quark_s9 strange_quark_s10) (.arrow strange_quark_l11 strange_quark_s10 strange_quark_s11)))))) (.seq (.arrow strange_quark_l12 (tensorProduct strange_quark_s6 strange_quark_s11) strange_quark_s12) (.seq (.arrow strange_quark_l13 strange_quark_s12 strange_quark_s13) (.arrow strange_quark_l14 strange_quark_s13 strange_quark_s14))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def strange_quark_true_arm : IGProtocol strange_quark_initial strange_quark_s14 :=
  (strange_quark_protocol).restrictToEVALT

-- false arm
noncomputable def strange_quark_false_arm : IGProtocol strange_quark_initial strange_quark_s14 :=
  (strange_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def strange_quark_tier_ground : OuroboricityTier := TierFunctor.obj strange_quark_initial
def strange_quark_tier : OuroboricityTier := TierFunctor.obj strange_quark_s14
#eval strange_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval strange_quark_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem strange_quark_frobenius :
    igFrobeniusAlg.mul strange_quark_initial strange_quark_initial = strange_quark_initial :=
  igFrobAlg_self_fusion strange_quark_initial

theorem strange_quark_protocol_depth :
    strange_quark_protocol.depth = 12 := by rfl

end Imscribing