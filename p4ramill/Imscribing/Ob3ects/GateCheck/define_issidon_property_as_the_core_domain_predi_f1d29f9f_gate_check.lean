-- IGProtocol scaffold: VINIT → CLINK → CLINK → CLINK → CLINK → FSPLIT → EVALT → EVALF → CLINK → CLINK → CLINK → FFUSE → CLINK → IFIX → TANCH → IMSCRIB
-- Class: Define IsSidon property as the core domain predicate
-- Fingerprint: sig=(11,2,2,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=16
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(5, 11)]

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
--   [3] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] CLINK     fid    := 𐑱               𐑱 → 𐑚  | composition — regime coherence
--   [5] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [6] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [7] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [8] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [9] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [10] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [11] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [12] CLINK     fid    := 𐑱               𐑙 → 𐑭  | composition — regime coherence
--   [13] IFIX      prot   := 𐑭               𐑱 → 𐑡  | irreversible fixation — winding number
--   [14] TANCH     top    := 𐑡               𐑭 → 𐑠  | terminal object — connectivity boundary
--   [15] IMSCRIB   gram   := 𐑠               𐑡 → 𐑼  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def define_issidon_property_as_the_core_ff15a0_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def define_issidon_property_as_the_core_ff15a0_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def define_issidon_property_as_the_core_ff15a0_s15 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def define_issidon_property_as_the_core_ff15a0_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def define_issidon_property_as_the_core_ff15a0_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def define_issidon_property_as_the_core_ff15a0_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def define_issidon_property_as_the_core_ff15a0_protocol : IGProtocol define_issidon_property_as_the_core_ff15a0_s0 define_issidon_property_as_the_core_ff15a0_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct define_issidon_property_as_the_core_ff15a0_s11 define_issidon_property_as_the_core_ff15a0_s11 = define_issidon_property_as_the_core_ff15a0_s11 (idempotent)
  (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l0 define_issidon_property_as_the_core_ff15a0_s0 define_issidon_property_as_the_core_ff15a0_s1) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l1 define_issidon_property_as_the_core_ff15a0_s1 define_issidon_property_as_the_core_ff15a0_s2) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l2 define_issidon_property_as_the_core_ff15a0_s2 define_issidon_property_as_the_core_ff15a0_s3) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l3 define_issidon_property_as_the_core_ff15a0_s3 define_issidon_property_as_the_core_ff15a0_s4) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l4 define_issidon_property_as_the_core_ff15a0_s4 define_issidon_property_as_the_core_ff15a0_s5) (.seq (.prod (.arrow define_issidon_property_as_the_core_ff15a0_l5 define_issidon_property_as_the_core_ff15a0_s5 define_issidon_property_as_the_core_ff15a0_s11) (.arrow define_issidon_property_as_the_core_ff15a0_l5 define_issidon_property_as_the_core_ff15a0_s5 define_issidon_property_as_the_core_ff15a0_s11)) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l11 define_issidon_property_as_the_core_ff15a0_s11 define_issidon_property_as_the_core_ff15a0_s11) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l11 define_issidon_property_as_the_core_ff15a0_s11 define_issidon_property_as_the_core_ff15a0_s12) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l12 define_issidon_property_as_the_core_ff15a0_s12 define_issidon_property_as_the_core_ff15a0_s13) (.seq (.arrow define_issidon_property_as_the_core_ff15a0_l13 define_issidon_property_as_the_core_ff15a0_s13 define_issidon_property_as_the_core_ff15a0_s14) (.arrow define_issidon_property_as_the_core_ff15a0_l14 define_issidon_property_as_the_core_ff15a0_s14 define_issidon_property_as_the_core_ff15a0_s15)))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def define_issidon_property_as_the_core_ff15a0_true_arm : IGProtocol define_issidon_property_as_the_core_ff15a0_s0 define_issidon_property_as_the_core_ff15a0_s15 :=
  (define_issidon_property_as_the_core_ff15a0_protocol).restrictToEVALT

-- false arm
noncomputable def define_issidon_property_as_the_core_ff15a0_false_arm : IGProtocol define_issidon_property_as_the_core_ff15a0_s0 define_issidon_property_as_the_core_ff15a0_s15 :=
  (define_issidon_property_as_the_core_ff15a0_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def define_issidon_property_as_the_core_ff15a0_tier_ground : OuroboricityTier := TierFunctor.obj define_issidon_property_as_the_core_ff15a0_s0
def define_issidon_property_as_the_core_ff15a0_tier : OuroboricityTier := TierFunctor.obj define_issidon_property_as_the_core_ff15a0_s15
#eval define_issidon_property_as_the_core_ff15a0_tier_ground  -- tier of the ground (pre-transformation)
#eval define_issidon_property_as_the_core_ff15a0_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem define_issidon_property_as_the_core_ff15a0_frobenius :
    igFrobeniusAlg.mul define_issidon_property_as_the_core_ff15a0_s0 define_issidon_property_as_the_core_ff15a0_s0 = define_issidon_property_as_the_core_ff15a0_s0 :=
  igFrobAlg_self_fusion define_issidon_property_as_the_core_ff15a0_s0
