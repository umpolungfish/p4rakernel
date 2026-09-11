-- IGProtocol scaffold: IMSCRIB → AREV → FSPLIT → AFWD → FFUSE → CLINK → IFIX → IMSCRIB
-- Class: Tibetan sand mandala: a intricate geometric painting made of colored sand, ritually destroyed upon completion. FSPLIT: the monks construct the mandala by placing individual grains, splitting the unified void into the elaborate palace of the deity with its four gates, concentric rings, and central lotus. FFUSE: the destruction ceremony sweeps the mandala into a single pile of mixed sand — reconstituting the multiplicity back into undifferentiated matter, which is then poured into a river. VINIT: the empty platform. TANCH: the outer ring of the mandala — the boundary of the sacred cosmos. AFWD: adding sand (creation). AREV: sweeping sand (dissolution). ENGAGR: the mandala is simultaneously a permanent spiritual reality and a transient material object.
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
private def tibetan_sand_mandala_a_intricate_34e6ff_s0 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_s6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def tibetan_sand_mandala_a_intricate_34e6ff_s7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
  --
-- ── Label Imscriptions (per-node delta) ─────────────────────
private def tibetan_sand_mandala_a_intricate_34e6ff_l0 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def tibetan_sand_mandala_a_intricate_34e6ff_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def tibetan_sand_mandala_a_intricate_34e6ff_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
  --
-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def tibetan_sand_mandala_a_intricate_34e6ff_protocol : IGProtocol tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s7 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct tibetan_sand_mandala_a_intricate_34e6ff_s4 tibetan_sand_mandala_a_intricate_34e6ff_s4 = tibetan_sand_mandala_a_intricate_34e6ff_s4 (idempotent)
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s1) (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l1 tibetan_sand_mandala_a_intricate_34e6ff_s1 tibetan_sand_mandala_a_intricate_34e6ff_s2) (.seq (.prod (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l2 tibetan_sand_mandala_a_intricate_34e6ff_s2 tibetan_sand_mandala_a_intricate_34e6ff_s4) (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l2 tibetan_sand_mandala_a_intricate_34e6ff_s2 tibetan_sand_mandala_a_intricate_34e6ff_s4)) (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l4 tibetan_sand_mandala_a_intricate_34e6ff_s4 tibetan_sand_mandala_a_intricate_34e6ff_s4) (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l4 tibetan_sand_mandala_a_intricate_34e6ff_s4 tibetan_sand_mandala_a_intricate_34e6ff_s5) (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l5 tibetan_sand_mandala_a_intricate_34e6ff_s5 tibetan_sand_mandala_a_intricate_34e6ff_s6) (.arrow tibetan_sand_mandala_a_intricate_34e6ff_l6 tibetan_sand_mandala_a_intricate_34e6ff_s6 tibetan_sand_mandala_a_intricate_34e6ff_s7)))))))
  --
-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₀.
def tibetan_sand_mandala_a_intricate_34e6ff_tier : OuroboricityTier := TierFunctor.obj tibetan_sand_mandala_a_intricate_34e6ff_s0
#eval tibetan_sand_mandala_a_intricate_34e6ff_tier  -- the Grammar's own verdict on its tier

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem tibetan_sand_mandala_a_intricate_34e6ff_frobenius :
    igFrobeniusAlg.mul tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 = tibetan_sand_mandala_a_intricate_34e6ff_s0 :=
  igFrobAlg_self_fusion tibetan_sand_mandala_a_intricate_34e6ff_s0
  --
-- Self-reference: Δ is a dagger and μ = Δ†
theorem tibetan_sand_mandala_a_intricate_34e6ff_self_ref :
    (igProtoDelta tibetan_sand_mandala_a_intricate_34e6ff_s0 (by decide)).isDagger = true ∧
    igProtoMu_depth (paralogical_dagger (by decide)) = 1 := by
  constructor
  · exact igProtoCopy_isDagger
  · exact igProtoMu_depth
  --
-- Loop closure: period=8, depth=1
theorem tibetan_sand_mandala_a_intricate_34e6ff_loop_closure :
    ∃ (loop : IGProtocol tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s7),
      loop = tibetan_sand_mandala_a_intricate_34e6ff_protocol ∧
      loop.period = 8 ∧ loop.depth = 1 := by
  exact ⟨_, rfl, by decide, by decide⟩
  --
-- igProtoCopy_isDagger licenses IMSCRIB→IFIX burn
-- CLINK→IMSCRIB weighted edge: .seq continuation

-- ─────────────────────────────────────────────────────────────────────────────
-- Conventional-expression register (Class: Tibetan sand mandala: a intricate geometric painting made of colored sand, ritually destroyed upon completion. FSPLIT: the monks construct the mandala by placing individual grains, splitting the unified void into the elaborate palace of the deity with its four gates, concentric rings, and central lotus. FFUSE: the destruction ceremony sweeps the mandala into a single pile of mixed sand — reconstituting the multiplicity back into undifferentiated matter, which is then poured into a river. VINIT: the empty platform. TANCH: the outer ring of the mandala — the boundary of the sacred cosmos. AFWD: adding sand (creation). AREV: sweeping sand (dissolution). ENGAGR: the mandala is simultaneously a permanent spiritual reality and a transient material object.)
--   Word: ⊙≺∈≻∋⋈⊡⊙
-- ─────────────────────────────────────────────────────────────────────────────

def tibetan_sand_mandala_a_intricate_34e6ff_opcodes : List String := ["IMSCRIB", "AREV", "FSPLIT", "AFWD", "FFUSE", "CLINK", "IFIX", "IMSCRIB"]

def tibetan_sand_mandala_a_intricate_34e6ff_conventional_register : List ConventionalExpr :=
  conventionalRegisterOf tibetan_sand_mandala_a_intricate_34e6ff_opcodes

def tibetan_sand_mandala_a_intricate_34e6ff_glyph_word : String := glyphWordOf tibetan_sand_mandala_a_intricate_34e6ff_opcodes

/-- The register has exactly one entry per opcode. -/
theorem tibetan_sand_mandala_a_intricate_34e6ff_register_length : tibetan_sand_mandala_a_intricate_34e6ff_conventional_register.length = 8 := by
  native_decide

/-- The register's opcode column reproduces the glyph word exactly. -/
theorem tibetan_sand_mandala_a_intricate_34e6ff_register_matches_word : tibetan_sand_mandala_a_intricate_34e6ff_glyph_word = "⊙≺∈≻∋⋈⊡⊙" := by
  native_decide

/-- The conventional protocol: a fixed-point walk over the ground imscription,
    each arrow annotated by its conventional expression. -/
def tibetan_sand_mandala_a_intricate_34e6ff_conventional_protocol : IGProtocol tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 :=
  .withGram Grammar.measure <|
  .withMem wool <|
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- IMSCRIB
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- AREV
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- FSPLIT
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- AFWD
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- FFUSE
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- CLINK
  (.seq (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0)  -- IFIX
  (.arrow tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0 tibetan_sand_mandala_a_intricate_34e6ff_s0))))))))  -- IMSCRIB

/-- The conventional protocol carries all 8 arrows. -/
theorem tibetan_sand_mandala_a_intricate_34e6ff_conventional_protocol_depth : tibetan_sand_mandala_a_intricate_34e6ff_conventional_protocol.depth = 8 := by
  native_decide

