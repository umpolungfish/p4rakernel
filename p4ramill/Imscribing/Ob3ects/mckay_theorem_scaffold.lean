-- IGProtocol scaffold: VINIT → TANCH → IMSCRIB → FSPLIT → AFWD → EVALT → CLINK → AREV → EVALF → CLINK → FFUSE → IFIX → ENGAGR → IMSCRIB → CLINK → TANCH
-- Class: McKay Theorem
-- Fingerprint: sig=(10,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=16
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(3, 10)]

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
--   [1] TANCH     top    := 𐑡               𐑼 → 𐑠  | terminal object — connectivity boundary
--   [2] IMSCRIB   gram   := 𐑠               𐑡 → 𐑚  | identity — self-imscription
--   [3] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] AFWD      rel    := 𐑾               𐑚 → 𐑙  | forward morphism — bidirectional arrow
--   [5] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [6] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [9] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [10] FFUSE     stoi   := 𐑙               𐑙 → 𐑭  | fuse μ — assembly mode
--   [11] IFIX      prot   := 𐑭               𐑙 → 𐑳  | irreversible fixation — winding number
--   [12] ENGAGR    stoi   := 𐑳               𐑭 → 𐑠  | engage paradox — B-state, both arms
--   [13] IMSCRIB   gram   := 𐑠               𐑳 → 𐑱  | identity — self-imscription
--   [14] CLINK     fid    := 𐑱               𐑠 → 𐑡  | composition — regime coherence
--   [15] TANCH     top    := 𐑡               𐑱 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def mckay_theorem_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def mckay_theorem_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def mckay_theorem_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def mckay_theorem_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def mckay_theorem_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def mckay_theorem_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def mckay_theorem_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def mckay_theorem_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def mckay_theorem_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def mckay_theorem_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def mckay_theorem_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def mckay_theorem_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def mckay_theorem_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def mckay_theorem_protocol : IGProtocol mckay_theorem_s0 mckay_theorem_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct mckay_theorem_s10 mckay_theorem_s10 = mckay_theorem_s10 (idempotent)
  (.seq (.arrow mckay_theorem_l0 mckay_theorem_s0 mckay_theorem_s1) (.seq (.arrow mckay_theorem_l1 mckay_theorem_s1 mckay_theorem_s2) (.seq (.arrow mckay_theorem_l2 mckay_theorem_s2 mckay_theorem_s3) (.seq (.prod (.arrow mckay_theorem_l3 mckay_theorem_s3 mckay_theorem_s10) (.arrow mckay_theorem_l3 mckay_theorem_s3 mckay_theorem_s10)) (.seq (.arrow mckay_theorem_l10 mckay_theorem_s10 mckay_theorem_s10) (.seq (.arrow mckay_theorem_l10 mckay_theorem_s10 mckay_theorem_s11) (.seq (.arrow mckay_theorem_l11 mckay_theorem_s11 mckay_theorem_s12) (.seq (.arrow mckay_theorem_l12 mckay_theorem_s12 mckay_theorem_s13) (.seq (.arrow mckay_theorem_l13 mckay_theorem_s13 mckay_theorem_s14) (.arrow mckay_theorem_l14 mckay_theorem_s14 mckay_theorem_s15))))))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def mckay_theorem_true_arm : IGProtocol mckay_theorem_s0 mckay_theorem_s15 :=
  (mckay_theorem_protocol).restrictToEVALT
  --
-- false arm
noncomputable def mckay_theorem_false_arm : IGProtocol mckay_theorem_s0 mckay_theorem_s15 :=
  (mckay_theorem_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def mckay_theorem_tier : OuroboricityTier := TierFunctor.obj mckay_theorem_s0
#eval mckay_theorem_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem mckay_theorem_frobenius :
    igFrobeniusAlg.mul mckay_theorem_s0 mckay_theorem_s0 = mckay_theorem_s0 :=
  igFrobAlg_self_fusion mckay_theorem_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: McKay Theorem)
--   Word: ⊢⊣⊙∈≻⊤⋈≺⊥⋈∋⊡⊞⊙⋈⊣
-- ─────────────────────────────────────────────────────────────────────────────

def mckay_theorem_opcodes : List String := ["VINIT", "TANCH", "IMSCRIB", "FSPLIT", "AFWD", "EVALT", "CLINK", "AREV", "EVALF", "CLINK", "FFUSE", "IFIX", "ENGAGR", "IMSCRIB", "CLINK", "TANCH"]

def mckay_theorem_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf mckay_theorem_opcodes

def mckay_theorem_glyph_word : String := glyphWordOf mckay_theorem_opcodes

/-- The register has exactly one entry per opcode. -/
theorem mckay_theorem_register_length : mckay_theorem_conventional_register.length = 16 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem mckay_theorem_register_matches_word : mckay_theorem_glyph_word = "⊢⊣⊙∈≻⊤⋈≺⊥⋈∋⊡⊞⊙⋈⊣" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def mckay_theorem_conventional_protocol : IGProtocol mckay_theorem_s0 mckay_theorem_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- VINIT
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- TANCH
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- IMSCRIB
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- FSPLIT
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- AFWD
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- EVALT
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- CLINK
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- AREV
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- EVALF
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- CLINK
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- FFUSE
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- IFIX
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- ENGAGR
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- IMSCRIB
  (.seq (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0)  -- CLINK
  (.arrow mckay_theorem_s0 mckay_theorem_s0 mckay_theorem_s0))))))))))))))))  -- TANCH

/-- The conventional protocol carries all 16 arrows. -/
theorem mckay_theorem_conventional_protocol_depth : mckay_theorem_conventional_protocol.depth = 16 := by
  native_decide

