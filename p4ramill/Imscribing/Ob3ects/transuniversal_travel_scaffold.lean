-- IGProtocol scaffold: VINIT → IMSCRIB → AFWD → CLINK → FSPLIT → EVALT → EVALF → ENGAGR → FFUSE → IMSCRIB → IFIX → TANCH
-- Class: transuniversal travel
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=12
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(4, 8)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
     --
-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑠  | initial object — ground of distinction
--   [1] IMSCRIB   gram   := 𐑠               𐑼 → 𐑾  | identity — self-imscription
--   [2] AFWD      rel    := 𐑾               𐑠 → 𐑱  | forward morphism — bidirectional arrow
--   [3] CLINK     fid    := 𐑱               𐑾 → 𐑚  | composition — regime coherence
--   [4] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [6] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [7] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [8] FFUSE     stoi   := 𐑙               𐑙 → 𐑠  | fuse μ — assembly mode
--   [9] IMSCRIB   gram   := 𐑠               𐑙 → 𐑭  | identity — self-imscription
--   [10] IFIX      prot   := 𐑭               𐑠 → 𐑡  | irreversible fixation — winding number
--   [11] TANCH     top    := 𐑡               𐑭 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def transuniversal_travel_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def transuniversal_travel_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def transuniversal_travel_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def transuniversal_travel_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def transuniversal_travel_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def transuniversal_travel_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def transuniversal_travel_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def transuniversal_travel_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def transuniversal_travel_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def transuniversal_travel_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def transuniversal_travel_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def transuniversal_travel_protocol : IGProtocol transuniversal_travel_s0 transuniversal_travel_s11 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct transuniversal_travel_s8 transuniversal_travel_s8 = transuniversal_travel_s8 (idempotent)
  (.seq (.arrow transuniversal_travel_l0 transuniversal_travel_s0 transuniversal_travel_s1) (.seq (.arrow transuniversal_travel_l1 transuniversal_travel_s1 transuniversal_travel_s2) (.seq (.arrow transuniversal_travel_l2 transuniversal_travel_s2 transuniversal_travel_s3) (.seq (.arrow transuniversal_travel_l3 transuniversal_travel_s3 transuniversal_travel_s4) (.seq (.prod (.arrow transuniversal_travel_l4 transuniversal_travel_s4 transuniversal_travel_s8) (.arrow transuniversal_travel_l4 transuniversal_travel_s4 transuniversal_travel_s8)) (.seq (.arrow transuniversal_travel_l8 transuniversal_travel_s8 transuniversal_travel_s8) (.seq (.arrow transuniversal_travel_l8 transuniversal_travel_s8 transuniversal_travel_s9) (.seq (.arrow transuniversal_travel_l9 transuniversal_travel_s9 transuniversal_travel_s10) (.arrow transuniversal_travel_l10 transuniversal_travel_s10 transuniversal_travel_s11)))))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def transuniversal_travel_true_arm : IGProtocol transuniversal_travel_s0 transuniversal_travel_s11 :=
  (transuniversal_travel_protocol).restrictToEVALT
  --
-- false arm
noncomputable def transuniversal_travel_false_arm : IGProtocol transuniversal_travel_s0 transuniversal_travel_s11 :=
  (transuniversal_travel_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def transuniversal_travel_tier : OuroboricityTier := TierFunctor.obj transuniversal_travel_s0
#eval transuniversal_travel_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem transuniversal_travel_frobenius :
    igFrobeniusAlg.mul transuniversal_travel_s0 transuniversal_travel_s0 = transuniversal_travel_s0 :=
  igFrobAlg_self_fusion transuniversal_travel_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: transuniversal travel)
--   Word: ⊢⊙≻⋈∈⊤⊥⊞∋⊙⊡⊣
-- ─────────────────────────────────────────────────────────────────────────────

def transuniversal_travel_opcodes : List String := ["VINIT", "IMSCRIB", "AFWD", "CLINK", "FSPLIT", "EVALT", "EVALF", "ENGAGR", "FFUSE", "IMSCRIB", "IFIX", "TANCH"]

def transuniversal_travel_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf transuniversal_travel_opcodes

def transuniversal_travel_glyph_word : String := glyphWordOf transuniversal_travel_opcodes

/-- The register has exactly one entry per opcode. -/
theorem transuniversal_travel_register_length : transuniversal_travel_conventional_register.length = 12 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem transuniversal_travel_register_matches_word : transuniversal_travel_glyph_word = "⊢⊙≻⋈∈⊤⊥⊞∋⊙⊡⊣" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def transuniversal_travel_conventional_protocol : IGProtocol transuniversal_travel_s0 transuniversal_travel_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- VINIT
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- IMSCRIB
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- AFWD
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- CLINK
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- FSPLIT
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- EVALT
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- EVALF
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- ENGAGR
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- FFUSE
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- IMSCRIB
  (.seq (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0)  -- IFIX
  (.arrow transuniversal_travel_s0 transuniversal_travel_s0 transuniversal_travel_s0))))))))))))  -- TANCH

/-- The conventional protocol carries all 12 arrows. -/
theorem transuniversal_travel_conventional_protocol_depth : transuniversal_travel_conventional_protocol.depth = 12 := by
  native_decide

