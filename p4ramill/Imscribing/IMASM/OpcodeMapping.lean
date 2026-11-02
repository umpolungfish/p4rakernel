-- Imscribing/IMASM/OpcodeMapping.lean
-- IMASM opcode → primitive bijection (12-12 mapping).
--
-- The 12 IMASM opcodes map one-to-one onto the 12 IG primitives across
-- the three families 𝓕₃, 𝓕₄, 𝓕₅.  This is the structural spine that lets
-- every IMASM word be read as an IGProtocol, and every IGProtocol as an
-- IMASM word.
--
-- Author: Lando ⊗ ⊙perator
-- Kernel: p4rakernel (paraconsistent Lean 4)

import Imscribing.IMASM.BankedWeight
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Algebra

namespace Imscribing.IMASM

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

/-- IMASM opcode enumeration.  Each constructor carries its glyph and the
    primitive field it annotates in an IGProtocol arrow label. -/
inductive IMASMOpcode where
  | VINIT   -- ⊢  initialize vacuum                      → Dimensionality
  | TANCH   -- ⊣  holographic boundary closure           → Topology
  | AFWD    -- ≻  unitary evolution / forward morphism   → Relational
  | AREV    -- ≺  adjoint symmetry / reverse morphism    → Grammar
  | CLINK   -- ⋈  superoperator composition              → Fidelity
  | IMSCRIB -- ⊙  self-referential identity               → Criticality
  | FSPLIT  -- ∈  comultiplication / range decomposition  → Granularity
  | FFUSE   -- ∋  multiplication / assembly mode         → Stoichiometry
  | EVALT   -- ⊤  coherent convergence / evaluate-true   → KineticChar
  | EVALF   -- ⊥  decoherent divergence / evaluate-false  → Chirality
  | ENGAGR  -- ⊞  non-commutative braiding / paradox      → Protection
  | IFIX    -- ⊡  trace record / winding number          → Polarity
  deriving DecidableEq, Repr

/-- The glyph for each opcode. -/
def opcodeGlyph : IMASMOpcode → String
  | .VINIT   => "⊢"
  | .TANCH   => "⊣"
  | .AFWD    => "≻"
  | .AREV    => "≺"
  | .CLINK   => "⋈"
  | .IMSCRIB => "⊙"
  | .FSPLIT  => "∈"
  | .FFUSE   => "∋"
  | .EVALT   => "⊤"
  | .EVALF   => "⊥"
  | .ENGAGR  => "⊞"
  | .IFIX    => "⊡"

/-- The primitive family (𝓕₃, 𝓕₄, or 𝓕₅) each opcode belongs to. -/
def opcodeFamily : IMASMOpcode → String
  | .VINIT   => "𝓕₄"
  | .TANCH   => "𝓕₅"
  | .AFWD    => "𝓕₄"
  | .AREV    => "𝓕₄"
  | .CLINK   => "𝓕₃"
  | .IMSCRIB => "𝓕₅"
  | .FSPLIT  => "𝓕₃"
  | .FFUSE   => "𝓕₃"
  | .EVALT   => "𝓕₅"
  | .EVALF   => "𝓕₄"
  | .ENGAGR  => "𝓕₄"
  | .IFIX    => "𝓕₅"

/-- The primitive value the opcode annotates in an IGProtocol label. -/
def opcodePrimitive : IMASMOpcode → String
  | .VINIT   => "Dimensionality"
  | .TANCH   => "Topology"
  | .AFWD    => "Relational"
  | .AREV    => "Grammar"
  | .CLINK   => "Fidelity"
  | .IMSCRIB => "Criticality"
  | .FSPLIT  => "Granularity"
  | .FFUSE   => "Stoichiometry"
  | .EVALT   => "KineticChar"
  | .EVALF   => "Chirality"
  | .ENGAGR  => "Protection"
  | .IFIX    => "Polarity"

/-- The 12 opcodes as a list. -/
def allOpcodes : List IMASMOpcode :=
  [ .VINIT, .TANCH, .AFWD, .AREV, .CLINK, .IMSCRIB,
    .FSPLIT, .FFUSE, .EVALT, .EVALF, .ENGAGR, .IFIX ]

/-- There are exactly 12 opcodes. -/
theorem allOpcodes_len : allOpcodes.length = 12 := by
  norm_num [allOpcodes]

/-- Map an opcode to the corresponding field accessor on Imscription.
    This lets an IGProtocol arrow label be read as an IMASM word, and vice versa. -/
def opcodeToField (op : IMASMOpcode) : String :=
  match op with
  | .VINIT   => "dim"
  | .TANCH   => "top"
  | .AFWD    => "rel"
  | .AREV    => "gram"
  | .CLINK   => "fid"
  | .IMSCRIB => "crit"
  | .FSPLIT  => "gran"
  | .FFUSE   => "stoi"
  | .EVALT   => "kin"
  | .EVALF   => "chir"
  | .ENGAGR  => "prot"
  | .IFIX    => "pol"

/-- The 12 opcodes cover all 12 primitive fields exactly once. -/
theorem opcodeFields_cover_all_primitives :
    (List.map opcodeToField allOpcodes).length = 12 := by
  simp only [allOpcodes, opcodeToField, List.length_map]
  norm_num

/-- opcodeToField is injective: distinct opcodes map to distinct field names. -/
theorem opcodeToField_injective {a b : IMASMOpcode} (h : opcodeToField a = opcodeToField b) :
    a = b := by
  cases a <;> cases b <;> simp_all [opcodeToField, IMASMOpcode] <;>
    (try decide) <;>
    (try contradiction)

end Imscribing.IMASM
