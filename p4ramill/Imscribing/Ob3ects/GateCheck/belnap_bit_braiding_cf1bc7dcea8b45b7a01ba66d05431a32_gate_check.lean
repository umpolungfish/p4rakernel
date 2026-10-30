-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ⋈ → ⊥ → ⋈ → ⊞ → ∋ → ⊡ → ⊣
-- Class: belnap_bit_braiding
-- Fingerprint: sig=(5,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=11
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 8)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [6] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [7] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [8] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [9] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [10] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def belnap_bit_braiding_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def belnap_bit_braiding_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def belnap_bit_braiding_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def belnap_bit_braiding_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def belnap_bit_braiding_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def belnap_bit_braiding_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def belnap_bit_braiding_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def belnap_bit_braiding_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def belnap_bit_braiding_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def belnap_bit_braiding_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def belnap_bit_braiding_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def belnap_bit_braiding_protocol : IGProtocol belnap_bit_braiding_initial belnap_bit_braiding_s10 :=
  .withGram Grammar.measure <|
  (.seq (.arrow belnap_bit_braiding_l0 belnap_bit_braiding_initial belnap_bit_braiding_s0) (.seq (.arrow belnap_bit_braiding_l1 belnap_bit_braiding_s0 belnap_bit_braiding_s1) (.seq (.arrow belnap_bit_braiding_l2 belnap_bit_braiding_s1 belnap_bit_braiding_s2) (.seq (.prod (.seq (.arrow belnap_bit_braiding_l3 belnap_bit_braiding_s2 belnap_bit_braiding_s3) (.arrow belnap_bit_braiding_l4 belnap_bit_braiding_s3 belnap_bit_braiding_s4)) (.seq (.arrow belnap_bit_braiding_l5 belnap_bit_braiding_s2 belnap_bit_braiding_s5) (.seq (.arrow belnap_bit_braiding_l6 belnap_bit_braiding_s5 belnap_bit_braiding_s6) (.arrow belnap_bit_braiding_l7 belnap_bit_braiding_s6 belnap_bit_braiding_s7)))) (.seq (.arrow belnap_bit_braiding_l8 (tensorProduct belnap_bit_braiding_s4 belnap_bit_braiding_s7) belnap_bit_braiding_s8) (.seq (.arrow belnap_bit_braiding_l9 belnap_bit_braiding_s8 belnap_bit_braiding_s9) (.arrow belnap_bit_braiding_l10 belnap_bit_braiding_s9 belnap_bit_braiding_s10)))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def belnap_bit_braiding_true_arm : IGProtocol belnap_bit_braiding_initial belnap_bit_braiding_s10 :=
  (belnap_bit_braiding_protocol).restrictToEVALT

-- false arm
noncomputable def belnap_bit_braiding_false_arm : IGProtocol belnap_bit_braiding_initial belnap_bit_braiding_s10 :=
  (belnap_bit_braiding_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def belnap_bit_braiding_tier_ground : OuroboricityTier := TierFunctor.obj belnap_bit_braiding_initial
def belnap_bit_braiding_tier : OuroboricityTier := TierFunctor.obj belnap_bit_braiding_s10
#eval belnap_bit_braiding_tier_ground  -- tier of the ground (pre-transformation)
#eval belnap_bit_braiding_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem belnap_bit_braiding_frobenius :
    igFrobeniusAlg.mul belnap_bit_braiding_initial belnap_bit_braiding_initial = belnap_bit_braiding_initial :=
  igFrobAlg_self_fusion belnap_bit_braiding_initial

theorem belnap_bit_braiding_protocol_depth :
    belnap_bit_braiding_protocol.depth = 9 := by rfl

end Imscribing