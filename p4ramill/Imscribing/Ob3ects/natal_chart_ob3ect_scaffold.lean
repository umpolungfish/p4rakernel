-- IGProtocol scaffold: IMSCRIB → AREV → FSPLIT → AFWD → FFUSE → CLINK → IFIX → IMSCRIB
-- Class: Natal chart ob3ect: the astrological birth chart — a snapshot of planetary positions at the moment of birth, forming the 12 houses, aspects, and sign placements. FSPLIT: the birth moment splits the unified sky into 12 houses (the mundane sphere) and the planets into their sign dignities and debilities. FFUSE: aspect integration reconstitutes the chart — the trines, squares, conjunctions, and oppositions weave the scattered placements into one coherent personality signature. VINIT: the sky before the birth moment. TANCH: the 360-degree circle of the ecliptic. AFWD: a planet in direct motion. AREV: a planet in retrograde. ENGAGR: a planet on the cusp — simultaneously in two houses or two signs.
-- Fingerprint: sig=(5,2,0,1)
--   self_ref=True | frobenius_order=1
--   dialetheia_complete=False | period=8
-- Expected tier: O₀
-- FSPLIT/FFUSE pairs: [(2, 4)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.ConventionalRegister

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
     --
-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] IMSCRIB   gram   := 𐑠               𐑠 → 𐑗  | identity — self-imscription
--   [1] AREV      pol    := 𐑗               𐑠 → 𐑚  | reverse morphism — parity flip
--   [2] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] AFWD      rel    := 𐑾               𐑚 → 𐑙  | forward morphism — bidirectional arrow
--   [4] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [5] CLINK     fid    := 𐑱               𐑙 → 𐑭  | composition — regime coherence
--   [6] IFIX      prot   := 𐑭               𐑱 → 𐑠  | irreversible fixation — winding number
--   [7] IMSCRIB   gram   := 𐑠               𐑭 → 𐑠  | identity — self-imscription

-- ── Back-propagation edges (self-referential loop) ──────────────────────
--   IMSCRIB positions: [0, 7]
--   IFIX    positions: [6]
--   Back-prop: IMSCRIB→IFIX (LinFix) — igProtoCopy_isDagger axiom applies
--   Weighted: CLINK→IMSCRIB — feeds next winding via .seq after .prod

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def natal_chart_ob3ect_the_astrological_7e616c_s0 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_s6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def natal_chart_ob3ect_the_astrological_7e616c_s7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def natal_chart_ob3ect_the_astrological_7e616c_l0 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def natal_chart_ob3ect_the_astrological_7e616c_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def natal_chart_ob3ect_the_astrological_7e616c_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def natal_chart_ob3ect_the_astrological_7e616c_protocol : IGProtocol natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s7 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct natal_chart_ob3ect_the_astrological_7e616c_s4 natal_chart_ob3ect_the_astrological_7e616c_s4 = natal_chart_ob3ect_the_astrological_7e616c_s4 (idempotent)
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_l0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s1) (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_l1 natal_chart_ob3ect_the_astrological_7e616c_s1 natal_chart_ob3ect_the_astrological_7e616c_s2) (.seq (.prod (.arrow natal_chart_ob3ect_the_astrological_7e616c_l2 natal_chart_ob3ect_the_astrological_7e616c_s2 natal_chart_ob3ect_the_astrological_7e616c_s4) (.arrow natal_chart_ob3ect_the_astrological_7e616c_l2 natal_chart_ob3ect_the_astrological_7e616c_s2 natal_chart_ob3ect_the_astrological_7e616c_s4)) (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_l4 natal_chart_ob3ect_the_astrological_7e616c_s4 natal_chart_ob3ect_the_astrological_7e616c_s4) (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_l4 natal_chart_ob3ect_the_astrological_7e616c_s4 natal_chart_ob3ect_the_astrological_7e616c_s5) (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_l5 natal_chart_ob3ect_the_astrological_7e616c_s5 natal_chart_ob3ect_the_astrological_7e616c_s6) (.arrow natal_chart_ob3ect_the_astrological_7e616c_l6 natal_chart_ob3ect_the_astrological_7e616c_s6 natal_chart_ob3ect_the_astrological_7e616c_s7)))))))
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₀.
def natal_chart_ob3ect_the_astrological_7e616c_tier : OuroboricityTier := TierFunctor.obj natal_chart_ob3ect_the_astrological_7e616c_s0
#eval natal_chart_ob3ect_the_astrological_7e616c_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem natal_chart_ob3ect_the_astrological_7e616c_frobenius :
    igFrobeniusAlg.mul natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 = natal_chart_ob3ect_the_astrological_7e616c_s0 :=
  igFrobAlg_self_fusion natal_chart_ob3ect_the_astrological_7e616c_s0
  --
-- Self-reference: Δ is a dagger and μ = Δ†
theorem natal_chart_ob3ect_the_astrological_7e616c_self_ref :
    (igProtoDelta natal_chart_ob3ect_the_astrological_7e616c_s0 (by decide)).isDagger = true ∧
    igProtoMu_depth (paralogical_dagger (by decide)) = 1 := by
  constructor
  · exact igProtoCopy_isDagger
  · exact igProtoMu_depth
  --
-- Loop closure: period=8, depth=1
theorem natal_chart_ob3ect_the_astrological_7e616c_loop_closure :
    ∃ (loop : IGProtocol natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s7),
      loop = natal_chart_ob3ect_the_astrological_7e616c_protocol ∧
      loop.period = 8 ∧ loop.depth = 1 := by
  exact ⟨_, rfl, by decide, by decide⟩
  --
-- igProtoCopy_isDagger licenses IMSCRIB→IFIX burn
-- CLINK→IMSCRIB weighted edge: .seq continuation

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: Natal chart ob3ect: the astrological birth chart — a snapshot of planetary positions at the moment of birth, forming the 12 houses, aspects, and sign placements. FSPLIT: the birth moment splits the unified sky into 12 houses (the mundane sphere) and the planets into their sign dignities and debilities. FFUSE: aspect integration reconstitutes the chart — the trines, squares, conjunctions, and oppositions weave the scattered placements into one coherent personality signature. VINIT: the sky before the birth moment. TANCH: the 360-degree circle of the ecliptic. AFWD: a planet in direct motion. AREV: a planet in retrograde. ENGAGR: a planet on the cusp — simultaneously in two houses or two signs.)
--   Word: ⊙≺∈≻∋⋈⊡⊙
-- ─────────────────────────────────────────────────────────────────────────────

def natal_chart_ob3ect_the_astrological_7e616c_opcodes : List String := ["IMSCRIB", "AREV", "FSPLIT", "AFWD", "FFUSE", "CLINK", "IFIX", "IMSCRIB"]

def natal_chart_ob3ect_the_astrological_7e616c_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf natal_chart_ob3ect_the_astrological_7e616c_opcodes

def natal_chart_ob3ect_the_astrological_7e616c_glyph_word : String := glyphWordOf natal_chart_ob3ect_the_astrological_7e616c_opcodes

/-- The register has exactly one entry per opcode. -/
theorem natal_chart_ob3ect_the_astrological_7e616c_register_length : natal_chart_ob3ect_the_astrological_7e616c_conventional_register.length = 8 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem natal_chart_ob3ect_the_astrological_7e616c_register_matches_word : natal_chart_ob3ect_the_astrological_7e616c_glyph_word = "⊙≺∈≻∋⋈⊡⊙" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def natal_chart_ob3ect_the_astrological_7e616c_conventional_protocol : IGProtocol natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- IMSCRIB
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- AREV
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- FSPLIT
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- AFWD
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- FFUSE
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- CLINK
  (.seq (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0)  -- IFIX
  (.arrow natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0 natal_chart_ob3ect_the_astrological_7e616c_s0))))))))  -- IMSCRIB

/-- The conventional protocol carries all 8 arrows. -/
theorem natal_chart_ob3ect_the_astrological_7e616c_conventional_protocol_depth : natal_chart_ob3ect_the_astrological_7e616c_conventional_protocol.depth = 8 := by
  native_decide

