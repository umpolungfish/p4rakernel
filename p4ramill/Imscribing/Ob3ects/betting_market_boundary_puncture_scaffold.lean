-- IGProtocol scaffold: VINIT → TANCH → AFWD → AREV → CLINK → IMSCRIB → FSPLIT → AFWD → EVALT → AREV → EVALF → FFUSE → ENGAGR → CLINK → IMSCRIB → IFIX
-- Class: Betting Market Boundary Puncture
-- Fingerprint: sig=(10,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=16
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(6, 11)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
     --
-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑡  | initial object — ground of distinction
--   [1] TANCH     top    := 𐑡               𐑼 → 𐑾  | terminal object — connectivity boundary
--   [2] AFWD      rel    := 𐑾               𐑡 → 𐑗  | forward morphism — bidirectional arrow
--   [3] AREV      pol    := 𐑗               𐑾 → 𐑱  | reverse morphism — parity flip
--   [4] CLINK     fid    := 𐑱               𐑗 → 𐑠  | composition — regime coherence
--   [5] IMSCRIB   gram   := 𐑠               𐑱 → 𐑚  | identity — self-imscription
--   [6] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [7] AFWD      rel    := 𐑾               𐑚 → 𐑙  | forward morphism — bidirectional arrow
--   [8] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [9] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [10] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [11] FFUSE     stoi   := 𐑙               𐑙 → 𐑳  | fuse μ — assembly mode
--   [12] ENGAGR    stoi   := 𐑳               𐑙 → 𐑱  | engage paradox — B-state, both arms
--   [13] CLINK     fid    := 𐑱               𐑳 → 𐑠  | composition — regime coherence
--   [14] IMSCRIB   gram   := 𐑠               𐑱 → 𐑭  | identity — self-imscription
--   [15] IFIX      prot   := 𐑭               𐑠 → 𐑼  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def betting_market_boundary_puncture_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def betting_market_boundary_puncture_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def betting_market_boundary_puncture_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def betting_market_boundary_puncture_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def betting_market_boundary_puncture_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def betting_market_boundary_puncture_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def betting_market_boundary_puncture_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def betting_market_boundary_puncture_protocol : IGProtocol betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct betting_market_boundary_puncture_s11 betting_market_boundary_puncture_s11 = betting_market_boundary_puncture_s11 (idempotent)
  (.seq (.arrow betting_market_boundary_puncture_l0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s1) (.seq (.arrow betting_market_boundary_puncture_l1 betting_market_boundary_puncture_s1 betting_market_boundary_puncture_s2) (.seq (.arrow betting_market_boundary_puncture_l2 betting_market_boundary_puncture_s2 betting_market_boundary_puncture_s3) (.seq (.arrow betting_market_boundary_puncture_l3 betting_market_boundary_puncture_s3 betting_market_boundary_puncture_s4) (.seq (.arrow betting_market_boundary_puncture_l4 betting_market_boundary_puncture_s4 betting_market_boundary_puncture_s5) (.seq (.arrow betting_market_boundary_puncture_l5 betting_market_boundary_puncture_s5 betting_market_boundary_puncture_s6) (.seq (.prod (.arrow betting_market_boundary_puncture_l6 betting_market_boundary_puncture_s6 betting_market_boundary_puncture_s11) (.arrow betting_market_boundary_puncture_l6 betting_market_boundary_puncture_s6 betting_market_boundary_puncture_s11)) (.seq (.arrow betting_market_boundary_puncture_l11 betting_market_boundary_puncture_s11 betting_market_boundary_puncture_s11) (.seq (.arrow betting_market_boundary_puncture_l11 betting_market_boundary_puncture_s11 betting_market_boundary_puncture_s12) (.seq (.arrow betting_market_boundary_puncture_l12 betting_market_boundary_puncture_s12 betting_market_boundary_puncture_s13) (.seq (.arrow betting_market_boundary_puncture_l13 betting_market_boundary_puncture_s13 betting_market_boundary_puncture_s14) (.arrow betting_market_boundary_puncture_l14 betting_market_boundary_puncture_s14 betting_market_boundary_puncture_s15))))))))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def betting_market_boundary_puncture_true_arm : IGProtocol betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s15 :=
  (betting_market_boundary_puncture_protocol).restrictToEVALT
  --
-- false arm
noncomputable def betting_market_boundary_puncture_false_arm : IGProtocol betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s15 :=
  (betting_market_boundary_puncture_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def betting_market_boundary_puncture_tier : OuroboricityTier := TierFunctor.obj betting_market_boundary_puncture_s0
#eval betting_market_boundary_puncture_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem betting_market_boundary_puncture_frobenius :
    igFrobeniusAlg.mul betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 = betting_market_boundary_puncture_s0 :=
  igFrobAlg_self_fusion betting_market_boundary_puncture_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: Betting Market Boundary Puncture)
--   Word: ⊢⊣≻≺⋈⊙∈≻⊤≺⊥∋⊞⋈⊙⊡
-- ─────────────────────────────────────────────────────────────────────────────

def betting_market_boundary_puncture_opcodes : List String := ["VINIT", "TANCH", "AFWD", "AREV", "CLINK", "IMSCRIB", "FSPLIT", "AFWD", "EVALT", "AREV", "EVALF", "FFUSE", "ENGAGR", "CLINK", "IMSCRIB", "IFIX"]

def betting_market_boundary_puncture_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf betting_market_boundary_puncture_opcodes

def betting_market_boundary_puncture_glyph_word : String := glyphWordOf betting_market_boundary_puncture_opcodes

/-- The register has exactly one entry per opcode. -/
theorem betting_market_boundary_puncture_register_length : betting_market_boundary_puncture_conventional_register.length = 16 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem betting_market_boundary_puncture_register_matches_word : betting_market_boundary_puncture_glyph_word = "⊢⊣≻≺⋈⊙∈≻⊤≺⊥∋⊞⋈⊙⊡" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def betting_market_boundary_puncture_conventional_protocol : IGProtocol betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- VINIT
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- TANCH
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- AFWD
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- AREV
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- CLINK
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- IMSCRIB
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- FSPLIT
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- AFWD
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- EVALT
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- AREV
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- EVALF
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- FFUSE
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- ENGAGR
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- CLINK
  (.seq (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0)  -- IMSCRIB
  (.arrow betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0 betting_market_boundary_puncture_s0))))))))))))))))  -- IFIX

/-- The conventional protocol carries all 16 arrows. -/
theorem betting_market_boundary_puncture_conventional_protocol_depth : betting_market_boundary_puncture_conventional_protocol.depth = 16 := by
  native_decide

