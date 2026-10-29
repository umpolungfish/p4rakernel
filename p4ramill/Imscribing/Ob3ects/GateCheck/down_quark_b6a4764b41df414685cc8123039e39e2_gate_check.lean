-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⊥ → ⊞ → ∋ → ⋈ → ⋈ → ≺ → ⊤ → ∈ → ∋ → ⊞ → ⊡ → ⊙ → ⊥ → ≻ → ⊣ → ⊡ → ⊙
-- Class: down_quark
-- Fingerprint: sig=(10,4,6,2)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=22
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(3, 7), (12, 13)]

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
--   [5] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [6] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [7] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [8] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [9] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [10] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [15] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [16] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [19] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [20] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [21] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def down_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def down_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def down_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def down_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def down_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def down_quark_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def down_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def down_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def down_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def down_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def down_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def down_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def down_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def down_quark_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def down_quark_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def down_quark_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def down_quark_protocol : IGProtocol down_quark_initial down_quark_s21 :=
  .withGram Grammar.measure <|
  (.seq (.arrow down_quark_l0 down_quark_initial down_quark_s0) (.seq (.arrow down_quark_l1 down_quark_s0 down_quark_s1) (.seq (.arrow down_quark_l2 down_quark_s1 down_quark_s2) (.seq (.arrow down_quark_l3 down_quark_s2 down_quark_s3) (.seq (.prod (.arrow down_quark_l4 down_quark_s3 down_quark_s4) (.seq (.arrow down_quark_l5 down_quark_s3 down_quark_s5) (.arrow down_quark_l6 down_quark_s5 down_quark_s6))) (.seq (.arrow down_quark_l7 (tensorProduct down_quark_s4 down_quark_s6) down_quark_s7) (.seq (.arrow down_quark_l8 down_quark_s7 down_quark_s8) (.seq (.arrow down_quark_l9 down_quark_s8 down_quark_s9) (.seq (.arrow down_quark_l10 down_quark_s9 down_quark_s10) (.seq (.arrow down_quark_l11 down_quark_s10 down_quark_s11) (.seq (.arrow down_quark_l12 down_quark_s11 down_quark_s12) (.seq (.prod (.refl down_quark_s12) (.refl down_quark_s12)) (.seq (.arrow down_quark_l13 (tensorProduct down_quark_s12 down_quark_s12) down_quark_s13) (.seq (.arrow down_quark_l14 down_quark_s13 down_quark_s14) (.seq (.arrow down_quark_l15 down_quark_s14 down_quark_s15) (.seq (.arrow down_quark_l16 down_quark_s15 down_quark_s16) (.seq (.arrow down_quark_l17 down_quark_s16 down_quark_s17) (.seq (.arrow down_quark_l18 down_quark_s17 down_quark_s18) (.seq (.arrow down_quark_l19 down_quark_s18 down_quark_s19) (.seq (.arrow down_quark_l20 down_quark_s19 down_quark_s20) (.arrow down_quark_l21 down_quark_s20 down_quark_s21)))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def down_quark_true_arm : IGProtocol down_quark_initial down_quark_s21 :=
  (down_quark_protocol).restrictToEVALT

-- false arm
noncomputable def down_quark_false_arm : IGProtocol down_quark_initial down_quark_s21 :=
  (down_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def down_quark_tier_ground : OuroboricityTier := TierFunctor.obj down_quark_initial
def down_quark_tier : OuroboricityTier := TierFunctor.obj down_quark_s21
#eval down_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval down_quark_tier  -- the Grammar's tuple-tier verdict

theorem down_quark_protocol_depth :
    down_quark_protocol.depth = 21 := by rfl

end Imscribing