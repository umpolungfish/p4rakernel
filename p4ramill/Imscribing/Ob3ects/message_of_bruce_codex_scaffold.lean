-- IGProtocol scaffold: VINIT → AFWD → IMSCRIB → FSPLIT → CLINK → IFIX → ENGAGR → AREV → FSPLIT → EVALF → FFUSE → CLINK → EVALT → FFUSE → IMSCRIB → TANCH
-- Class: Message of Bruce Codex
-- Fingerprint: sig=(8,4,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=16
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(8, 10), (3, 13)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
     --
-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑾  | initial object — ground of distinction
--   [1] AFWD      rel    := 𐑾               𐑼 → 𐑠  | forward morphism — bidirectional arrow
--   [2] IMSCRIB   gram   := 𐑠               𐑾 → 𐑚  | identity — self-imscription
--   [3] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [5] IFIX      prot   := 𐑭               𐑚 → 𐑙  | irreversible fixation — winding number
--   [6] ENGAGR    stoi   := 𐑳               𐑚 → 𐑙  | engage paradox — B-state, both arms
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [11] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [12] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [13] FFUSE     stoi   := 𐑙               𐑙 → 𐑠  | fuse μ — assembly mode
--   [14] IMSCRIB   gram   := 𐑠               𐑙 → 𐑡  | identity — self-imscription
--   [15] TANCH     top    := 𐑡               𐑠 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def message_of_bruce_codex_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def message_of_bruce_codex_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def message_of_bruce_codex_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def message_of_bruce_codex_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def message_of_bruce_codex_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def message_of_bruce_codex_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := hung, prot := ah }
private def message_of_bruce_codex_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := hung, prot := ah }
private def message_of_bruce_codex_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def message_of_bruce_codex_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def message_of_bruce_codex_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def message_of_bruce_codex_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def message_of_bruce_codex_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def message_of_bruce_codex_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def message_of_bruce_codex_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def message_of_bruce_codex_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def message_of_bruce_codex_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def message_of_bruce_codex_protocol : IGProtocol message_of_bruce_codex_s0 message_of_bruce_codex_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct message_of_bruce_codex_s10 message_of_bruce_codex_s10 = message_of_bruce_codex_s10 (idempotent)
  (.seq (.arrow message_of_bruce_codex_l0 message_of_bruce_codex_s0 message_of_bruce_codex_s1) (.seq (.arrow message_of_bruce_codex_l1 message_of_bruce_codex_s1 message_of_bruce_codex_s2) (.seq (.arrow message_of_bruce_codex_l2 message_of_bruce_codex_s2 message_of_bruce_codex_s3) (.seq (.prod (.arrow message_of_bruce_codex_l3 message_of_bruce_codex_s3 message_of_bruce_codex_s10) (.arrow message_of_bruce_codex_l3 message_of_bruce_codex_s3 message_of_bruce_codex_s10)) (.seq (.arrow message_of_bruce_codex_l10 message_of_bruce_codex_s10 message_of_bruce_codex_s10) (.seq (.arrow message_of_bruce_codex_l10 message_of_bruce_codex_s10 message_of_bruce_codex_s11) (.seq (.arrow message_of_bruce_codex_l11 message_of_bruce_codex_s11 message_of_bruce_codex_s12) (.seq (.arrow message_of_bruce_codex_l12 message_of_bruce_codex_s12 message_of_bruce_codex_s13) (.seq (.arrow message_of_bruce_codex_l13 message_of_bruce_codex_s13 message_of_bruce_codex_s14) (.arrow message_of_bruce_codex_l14 message_of_bruce_codex_s14 message_of_bruce_codex_s15))))))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def message_of_bruce_codex_true_arm : IGProtocol message_of_bruce_codex_s0 message_of_bruce_codex_s15 :=
  (message_of_bruce_codex_protocol).restrictToEVALT
  --
-- false arm
noncomputable def message_of_bruce_codex_false_arm : IGProtocol message_of_bruce_codex_s0 message_of_bruce_codex_s15 :=
  (message_of_bruce_codex_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def message_of_bruce_codex_tier : OuroboricityTier := TierFunctor.obj message_of_bruce_codex_s0
#eval message_of_bruce_codex_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem message_of_bruce_codex_frobenius :
    igFrobeniusAlg.mul message_of_bruce_codex_s0 message_of_bruce_codex_s0 = message_of_bruce_codex_s0 :=
  igFrobAlg_self_fusion message_of_bruce_codex_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: Message of Bruce Codex)
--   Word: ⊢≻⊙∈⋈⊡⊞≺∈⊥∋⋈⊤∋⊙⊣
-- ─────────────────────────────────────────────────────────────────────────────

def message_of_bruce_codex_opcodes : List String := ["VINIT", "AFWD", "IMSCRIB", "FSPLIT", "CLINK", "IFIX", "ENGAGR", "AREV", "FSPLIT", "EVALF", "FFUSE", "CLINK", "EVALT", "FFUSE", "IMSCRIB", "TANCH"]

def message_of_bruce_codex_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf message_of_bruce_codex_opcodes

def message_of_bruce_codex_glyph_word : String := glyphWordOf message_of_bruce_codex_opcodes

/-- The register has exactly one entry per opcode. -/
theorem message_of_bruce_codex_register_length : message_of_bruce_codex_conventional_register.length = 16 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem message_of_bruce_codex_register_matches_word : message_of_bruce_codex_glyph_word = "⊢≻⊙∈⋈⊡⊞≺∈⊥∋⋈⊤∋⊙⊣" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def message_of_bruce_codex_conventional_protocol : IGProtocol message_of_bruce_codex_s0 message_of_bruce_codex_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- VINIT
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- AFWD
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- IMSCRIB
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- FSPLIT
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- CLINK
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- IFIX
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- ENGAGR
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- AREV
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- FSPLIT
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- EVALF
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- FFUSE
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- CLINK
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- EVALT
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- FFUSE
  (.seq (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0)  -- IMSCRIB
  (.arrow message_of_bruce_codex_s0 message_of_bruce_codex_s0 message_of_bruce_codex_s0))))))))))))))))  -- TANCH

/-- The conventional protocol carries all 16 arrows. -/
theorem message_of_bruce_codex_conventional_protocol_depth : message_of_bruce_codex_conventional_protocol.depth = 16 := by
  native_decide

