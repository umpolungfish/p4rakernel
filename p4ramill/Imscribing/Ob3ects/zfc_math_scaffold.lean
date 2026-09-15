-- IGProtocol scaffold: VINIT → IFIX → AFWD → CLINK → IFIX → FSPLIT → EVALT → ENGAGR → FFUSE → IMSCRIB → AREV → EVALF → TANCH
-- Class: zfc math
-- Fingerprint: sig=(6,2,3,2)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=13
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(5, 8)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
     --
-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑭  | initial object — ground of distinction
--   [1] IFIX      prot   := 𐑭               𐑼 → 𐑾  | irreversible fixation — winding number
--   [2] AFWD      rel    := 𐑾               𐑭 → 𐑱  | forward morphism — bidirectional arrow
--   [3] CLINK     fid    := 𐑱               𐑾 → 𐑭  | composition — regime coherence
--   [4] IFIX      prot   := 𐑭               𐑱 → 𐑚  | irreversible fixation — winding number
--   [5] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [6] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [7] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [8] FFUSE     stoi   := 𐑙               𐑙 → 𐑠  | fuse μ — assembly mode
--   [9] IMSCRIB   gram   := 𐑠               𐑙 → 𐑗  | identity — self-imscription
--   [10] AREV      pol    := 𐑗               𐑠 → 𐑖  | reverse morphism — parity flip
--   [11] EVALF     chir   := 𐑖               𐑗 → 𐑡  | evaluate-false — chirality check
--   [12] TANCH     top    := 𐑡               𐑖 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def zfc_math_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := up, prot := ah }
private def zfc_math_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def zfc_math_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def zfc_math_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def zfc_math_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def zfc_math_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def zfc_math_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def zfc_math_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def zfc_math_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def zfc_math_protocol : IGProtocol zfc_math_s0 zfc_math_s12 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct zfc_math_s8 zfc_math_s8 = zfc_math_s8 (idempotent)
  (.seq (.arrow zfc_math_l0 zfc_math_s0 zfc_math_s1) (.seq (.arrow zfc_math_l1 zfc_math_s1 zfc_math_s2) (.seq (.arrow zfc_math_l2 zfc_math_s2 zfc_math_s3) (.seq (.arrow zfc_math_l3 zfc_math_s3 zfc_math_s4) (.seq (.arrow zfc_math_l4 zfc_math_s4 zfc_math_s5) (.seq (.prod (.arrow zfc_math_l5 zfc_math_s5 zfc_math_s8) (.arrow zfc_math_l5 zfc_math_s5 zfc_math_s8)) (.seq (.arrow zfc_math_l8 zfc_math_s8 zfc_math_s8) (.seq (.arrow zfc_math_l8 zfc_math_s8 zfc_math_s9) (.seq (.arrow zfc_math_l9 zfc_math_s9 zfc_math_s10) (.seq (.arrow zfc_math_l10 zfc_math_s10 zfc_math_s11) (.arrow zfc_math_l11 zfc_math_s11 zfc_math_s12)))))))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def zfc_math_true_arm : IGProtocol zfc_math_s0 zfc_math_s12 :=
  (zfc_math_protocol).restrictToEVALT
  --
-- false arm
noncomputable def zfc_math_false_arm : IGProtocol zfc_math_s0 zfc_math_s12 :=
  (zfc_math_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def zfc_math_tier : OuroboricityTier := TierFunctor.obj zfc_math_s0
#eval zfc_math_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem zfc_math_frobenius :
    igFrobeniusAlg.mul zfc_math_s0 zfc_math_s0 = zfc_math_s0 :=
  igFrobAlg_self_fusion zfc_math_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: zfc math)
--   Word: ⊢⊡≻⋈⊡∈⊤⊞∋⊙≺⊥⊣
-- ─────────────────────────────────────────────────────────────────────────────

def zfc_math_opcodes : List String := ["VINIT", "IFIX", "AFWD", "CLINK", "IFIX", "FSPLIT", "EVALT", "ENGAGR", "FFUSE", "IMSCRIB", "AREV", "EVALF", "TANCH"]

def zfc_math_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf zfc_math_opcodes

def zfc_math_glyph_word : String := glyphWordOf zfc_math_opcodes

/-- The register has exactly one entry per opcode. -/
theorem zfc_math_register_length : zfc_math_conventional_register.length = 13 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem zfc_math_register_matches_word : zfc_math_glyph_word = "⊢⊡≻⋈⊡∈⊤⊞∋⊙≺⊥⊣" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def zfc_math_conventional_protocol : IGProtocol zfc_math_s0 zfc_math_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- VINIT
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- IFIX
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- AFWD
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- CLINK
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- IFIX
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- FSPLIT
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- EVALT
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- ENGAGR
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- FFUSE
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- IMSCRIB
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- AREV
  (.seq (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)  -- EVALF
  (.arrow zfc_math_s0 zfc_math_s0 zfc_math_s0)))))))))))))  -- TANCH

/-- The conventional protocol carries all 13 arrows. -/
theorem zfc_math_conventional_protocol_depth : zfc_math_conventional_protocol.depth = 13 := by
  native_decide

