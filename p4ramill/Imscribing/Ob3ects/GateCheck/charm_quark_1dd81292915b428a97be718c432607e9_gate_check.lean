-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⊡ → ∈ → ⊤ → ≻ → ⋈ → ≺ → ⊥ → ≻ → ⋈ → ⊞ → ∋ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ≺ → ⊥ → ≻ → ⋈ → ⊞ → ∋ → ⊡ → ⊣
-- Class: charm_quark
-- Fingerprint: sig=(15,4,6,2)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=27
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 13), (15, 24)]

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
--   [3] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [4] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [7] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [10] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [11] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [12] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [15] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [18] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [19] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [20] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [21] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [24] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def charm_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def charm_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def charm_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def charm_quark_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def charm_quark_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def charm_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def charm_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def charm_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def charm_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l17 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def charm_quark_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def charm_quark_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def charm_quark_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def charm_quark_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def charm_quark_protocol : IGProtocol charm_quark_initial charm_quark_s26 :=
  .withGram Grammar.measure <|
  (.seq (.arrow charm_quark_l0 charm_quark_initial charm_quark_s0) (.seq (.arrow charm_quark_l1 charm_quark_s0 charm_quark_s1) (.seq (.arrow charm_quark_l2 charm_quark_s1 charm_quark_s2) (.seq (.arrow charm_quark_l3 charm_quark_s2 charm_quark_s3) (.seq (.arrow charm_quark_l4 charm_quark_s3 charm_quark_s4) (.seq (.prod (.seq (.arrow charm_quark_l5 charm_quark_s4 charm_quark_s5) (.seq (.arrow charm_quark_l6 charm_quark_s5 charm_quark_s6) (.seq (.arrow charm_quark_l7 charm_quark_s6 charm_quark_s7) (.arrow charm_quark_l8 charm_quark_s7 charm_quark_s8)))) (.seq (.arrow charm_quark_l9 charm_quark_s4 charm_quark_s9) (.seq (.arrow charm_quark_l10 charm_quark_s9 charm_quark_s10) (.seq (.arrow charm_quark_l11 charm_quark_s10 charm_quark_s11) (.arrow charm_quark_l12 charm_quark_s11 charm_quark_s12))))) (.seq (.arrow charm_quark_l13 (tensorProduct charm_quark_s8 charm_quark_s12) charm_quark_s13) (.seq (.arrow charm_quark_l14 charm_quark_s13 charm_quark_s14) (.seq (.arrow charm_quark_l15 charm_quark_s14 charm_quark_s15) (.seq (.prod (.seq (.arrow charm_quark_l16 charm_quark_s15 charm_quark_s16) (.seq (.arrow charm_quark_l17 charm_quark_s16 charm_quark_s17) (.seq (.arrow charm_quark_l18 charm_quark_s17 charm_quark_s18) (.arrow charm_quark_l19 charm_quark_s18 charm_quark_s19)))) (.seq (.arrow charm_quark_l20 charm_quark_s15 charm_quark_s20) (.seq (.arrow charm_quark_l21 charm_quark_s20 charm_quark_s21) (.seq (.arrow charm_quark_l22 charm_quark_s21 charm_quark_s22) (.arrow charm_quark_l23 charm_quark_s22 charm_quark_s23))))) (.seq (.arrow charm_quark_l24 (tensorProduct charm_quark_s19 charm_quark_s23) charm_quark_s24) (.seq (.arrow charm_quark_l25 charm_quark_s24 charm_quark_s25) (.arrow charm_quark_l26 charm_quark_s25 charm_quark_s26)))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def charm_quark_true_arm : IGProtocol charm_quark_initial charm_quark_s26 :=
  (charm_quark_protocol).restrictToEVALT

-- false arm
noncomputable def charm_quark_false_arm : IGProtocol charm_quark_initial charm_quark_s26 :=
  (charm_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def charm_quark_tier_ground : OuroboricityTier := TierFunctor.obj charm_quark_initial
def charm_quark_tier : OuroboricityTier := TierFunctor.obj charm_quark_s26
#eval charm_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval charm_quark_tier  -- the Grammar's tuple-tier verdict

theorem charm_quark_protocol_depth :
    charm_quark_protocol.depth = 19 := by rfl

end Imscribing