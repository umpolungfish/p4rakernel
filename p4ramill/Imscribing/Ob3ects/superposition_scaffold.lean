-- IGProtocol scaffold: VINIT → AFWD → ENGAGR → FSPLIT → EVALT → EVALF → IMSCRIB → FFUSE → CLINK → IFIX
-- Class: superposition
-- Fingerprint: sig=(4,2,3,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=10
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: [(3, 7)]

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
--   [1] AFWD      rel    := 𐑾               𐑼 → 𐑳  | forward morphism — bidirectional arrow
--   [2] ENGAGR    stoi   := 𐑳               𐑾 → 𐑚  | engage paradox — B-state, both arms
--   [3] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [5] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [6] IMSCRIB   gram   := 𐑠               𐑚 → 𐑙  | identity — self-imscription
--   [7] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [8] CLINK     fid    := 𐑱               𐑙 → 𐑭  | composition — regime coherence
--   [9] IFIX      prot   := 𐑭               𐑱 → 𐑼  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def superposition_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def superposition_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def superposition_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := up, prot := awe }
private def superposition_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def superposition_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def superposition_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def superposition_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def superposition_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def superposition_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def superposition_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def superposition_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def superposition_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def superposition_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def superposition_protocol : IGProtocol superposition_s0 superposition_s9 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct superposition_s7 superposition_s7 = superposition_s7 (idempotent)
  (.seq (.arrow superposition_l0 superposition_s0 superposition_s1) (.seq (.arrow superposition_l1 superposition_s1 superposition_s2) (.seq (.arrow superposition_l2 superposition_s2 superposition_s3) (.seq (.prod (.arrow superposition_l3 superposition_s3 superposition_s7) (.arrow superposition_l3 superposition_s3 superposition_s7)) (.seq (.arrow superposition_l7 superposition_s7 superposition_s7) (.seq (.arrow superposition_l7 superposition_s7 superposition_s8) (.arrow superposition_l8 superposition_s8 superposition_s9)))))))
  --
-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def superposition_true_arm : IGProtocol superposition_s0 superposition_s9 :=
  (superposition_protocol).restrictToEVALT
  --
-- false arm
noncomputable def superposition_false_arm : IGProtocol superposition_s0 superposition_s9 :=
  (superposition_protocol).restrictToEVALF
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def superposition_tier : OuroboricityTier := TierFunctor.obj superposition_s0
#eval superposition_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem superposition_frobenius :
    igFrobeniusAlg.mul superposition_s0 superposition_s0 = superposition_s0 :=
  igFrobAlg_self_fusion superposition_s0

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: superposition)
--   Word: ⊢≻⊞∈⊤⊥⊙∋⋈⊡
-- ─────────────────────────────────────────────────────────────────────────────

def superposition_opcodes : List String := ["VINIT", "AFWD", "ENGAGR", "FSPLIT", "EVALT", "EVALF", "IMSCRIB", "FFUSE", "CLINK", "IFIX"]

def superposition_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf superposition_opcodes

def superposition_glyph_word : String := glyphWordOf superposition_opcodes

/-- The register has exactly one entry per opcode. -/
theorem superposition_register_length : superposition_conventional_register.length = 10 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem superposition_register_matches_word : superposition_glyph_word = "⊢≻⊞∈⊤⊥⊙∋⋈⊡" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def superposition_conventional_protocol : IGProtocol superposition_s0 superposition_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- VINIT
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- AFWD
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- ENGAGR
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- FSPLIT
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- EVALT
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- EVALF
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- IMSCRIB
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- FFUSE
  (.seq (.arrow superposition_s0 superposition_s0 superposition_s0)  -- CLINK
  (.arrow superposition_s0 superposition_s0 superposition_s0))))))))))  -- IFIX

/-- The conventional protocol carries all 10 arrows. -/
theorem superposition_conventional_protocol_depth : superposition_conventional_protocol.depth = 10 := by
  native_decide

