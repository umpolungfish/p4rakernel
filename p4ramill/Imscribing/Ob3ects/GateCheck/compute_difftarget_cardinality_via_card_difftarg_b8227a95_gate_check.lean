-- IGProtocol scaffold: VINIT → CLINK → CLINK → CLINK → FSPLIT → EVALT → EVALF → CLINK → CLINK → CLINK → FFUSE → CLINK → IFIX → TANCH → IMSCRIB
-- Class: Compute diffTarget cardinality via card_diffTarget theorem
-- Fingerprint: sig=(10,2,2,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=15
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(4, 10)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑱  | initial object — ground of distinction
--   [1] CLINK     fid    := 𐑱               𐑼 → 𐑱  | composition — regime coherence
--   [2] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [3] CLINK     fid    := 𐑱               𐑱 → 𐑚  | composition — regime coherence
--   [4] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [6] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [7] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [8] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [9] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [11] CLINK     fid    := 𐑱               𐑙 → 𐑭  | composition — regime coherence
--   [12] IFIX      prot   := 𐑭               𐑱 → 𐑡  | irreversible fixation — winding number
--   [13] TANCH     top    := 𐑡               𐑭 → 𐑠  | terminal object — connectivity boundary
--   [14] IMSCRIB   gram   := 𐑠               𐑡 → 𐑼  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def compute_difftarget_cardinality_via_card_812eb7_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def compute_difftarget_cardinality_via_card_812eb7_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def compute_difftarget_cardinality_via_card_812eb7_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def compute_difftarget_cardinality_via_card_812eb7_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def compute_difftarget_cardinality_via_card_812eb7_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def compute_difftarget_cardinality_via_card_812eb7_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def compute_difftarget_cardinality_via_card_812eb7_protocol : IGProtocol compute_difftarget_cardinality_via_card_812eb7_s0 compute_difftarget_cardinality_via_card_812eb7_s14 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct compute_difftarget_cardinality_via_card_812eb7_s10 compute_difftarget_cardinality_via_card_812eb7_s10 = compute_difftarget_cardinality_via_card_812eb7_s10 (idempotent)
  (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l0 compute_difftarget_cardinality_via_card_812eb7_s0 compute_difftarget_cardinality_via_card_812eb7_s1) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l1 compute_difftarget_cardinality_via_card_812eb7_s1 compute_difftarget_cardinality_via_card_812eb7_s2) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l2 compute_difftarget_cardinality_via_card_812eb7_s2 compute_difftarget_cardinality_via_card_812eb7_s3) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l3 compute_difftarget_cardinality_via_card_812eb7_s3 compute_difftarget_cardinality_via_card_812eb7_s4) (.seq (.prod (.arrow compute_difftarget_cardinality_via_card_812eb7_l4 compute_difftarget_cardinality_via_card_812eb7_s4 compute_difftarget_cardinality_via_card_812eb7_s10) (.arrow compute_difftarget_cardinality_via_card_812eb7_l4 compute_difftarget_cardinality_via_card_812eb7_s4 compute_difftarget_cardinality_via_card_812eb7_s10)) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l10 compute_difftarget_cardinality_via_card_812eb7_s10 compute_difftarget_cardinality_via_card_812eb7_s10) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l10 compute_difftarget_cardinality_via_card_812eb7_s10 compute_difftarget_cardinality_via_card_812eb7_s11) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l11 compute_difftarget_cardinality_via_card_812eb7_s11 compute_difftarget_cardinality_via_card_812eb7_s12) (.seq (.arrow compute_difftarget_cardinality_via_card_812eb7_l12 compute_difftarget_cardinality_via_card_812eb7_s12 compute_difftarget_cardinality_via_card_812eb7_s13) (.arrow compute_difftarget_cardinality_via_card_812eb7_l13 compute_difftarget_cardinality_via_card_812eb7_s13 compute_difftarget_cardinality_via_card_812eb7_s14))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def compute_difftarget_cardinality_via_card_812eb7_true_arm : IGProtocol compute_difftarget_cardinality_via_card_812eb7_s0 compute_difftarget_cardinality_via_card_812eb7_s14 :=
  (compute_difftarget_cardinality_via_card_812eb7_protocol).restrictToEVALT

-- false arm
noncomputable def compute_difftarget_cardinality_via_card_812eb7_false_arm : IGProtocol compute_difftarget_cardinality_via_card_812eb7_s0 compute_difftarget_cardinality_via_card_812eb7_s14 :=
  (compute_difftarget_cardinality_via_card_812eb7_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def compute_difftarget_cardinality_via_card_812eb7_tier_ground : OuroboricityTier := TierFunctor.obj compute_difftarget_cardinality_via_card_812eb7_s0
def compute_difftarget_cardinality_via_card_812eb7_tier : OuroboricityTier := TierFunctor.obj compute_difftarget_cardinality_via_card_812eb7_s14
#eval compute_difftarget_cardinality_via_card_812eb7_tier_ground  -- tier of the ground (pre-transformation)
#eval compute_difftarget_cardinality_via_card_812eb7_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem compute_difftarget_cardinality_via_card_812eb7_frobenius :
    igFrobeniusAlg.mul compute_difftarget_cardinality_via_card_812eb7_s0 compute_difftarget_cardinality_via_card_812eb7_s0 = compute_difftarget_cardinality_via_card_812eb7_s0 :=
  igFrobAlg_self_fusion compute_difftarget_cardinality_via_card_812eb7_s0
