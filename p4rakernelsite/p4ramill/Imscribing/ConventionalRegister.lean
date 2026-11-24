-- Imscribing/ConventionalRegister.lean
-- Shared ConventionalExpr infrastructure: the opcode → conventional-expression
-- translation used by every ob3ect scaffold. Defined ONCE so the 325 scaffold
-- files import it instead of each redefining `ConventionalExpr` and colliding.
--
-- The twelve opcodes ARE the twelve morphisms. Each morphism's conventional
-- expression is its category-theoretic reading — correct in every register,
-- with the domain-specific formula layered on top by each scaffold.

namespace Imscribing

/-- An opcode carries three registers: glyph, conventional formula, morphism. -/
structure ConventionalExpr where
  opcode   : String
  name     : String
  formula  : String
  morphism : String
deriving Repr, DecidableEq

/-- The universal morphism reading of each of the twelve opcodes. -/
def conventionalExprOf (opcode : String) : ConventionalExpr :=
  match opcode with
  | "VINIT"   => ⟨"VINIT",   "Initial object",    "! : ∅ → M",          "initial morphism"⟩
  | "TANCH"   => ⟨"TANCH",   "Terminal object",   "! : M → 1",          "terminal morphism"⟩
  | "AFWD"    => ⟨"AFWD",    "Forward morphism",  "f : A → B",          "arrow"⟩
  | "AREV"    => ⟨"AREV",    "Reverse morphism",  "f⁻¹ : B → A",        "reversal"⟩
  | "CLINK"   => ⟨"CLINK",   "Composition",       "g ∘ f",              "composition (∘)"⟩
  | "EVALT"   => ⟨"EVALT",   "Truth deposit",     "⊤ : 1 → B",          "deposit-T (truth arm)"⟩
  | "EVALF"   => ⟨"EVALF",   "False deposit",     "⊥ : 1 → B",          "deposit-F (false arm)"⟩
  | "FSPLIT"  => ⟨"FSPLIT",  "Comultiplication",  "δ : s → s⊗s",        "fork δ"⟩
  | "FFUSE"   => ⟨"FFUSE",   "Multiplication",    "μ : s⊗s → s",        "join μ"⟩
  | "IMSCRIB" => ⟨"IMSCRIB", "Identity",          "id : s → s",         "self-map"⟩
  | "ENGAGR"  => ⟨"ENGAGR",  "Belnap diagonal",   "B = T∧F",            "Belnap diagonal"⟩
  | "IFIX"    => ⟨"IFIX",    "Fixed point",       "fix f = f (fix f)",  "fix arrow"⟩
  | _         => ⟨opcode,    "unknown",           "?",                  "?"⟩

/-- Glyph for each opcode name. -/
def glyphOf (opcode : String) : String :=
  match opcode with
  | "VINIT" => "⊢" | "TANCH" => "⊣" | "AFWD" => "≻" | "AREV" => "≺"
  | "CLINK" => "⋈" | "EVALT" => "⊤" | "EVALF" => "⊥"
  | "FSPLIT" => "∈" | "FFUSE" => "∋" | "IMSCRIB" => "⊙"
  | "ENGAGR" => "⊞" | "IFIX" => "⊡" | _ => "?"

/-- Glyph word from an opcode-name sequence. -/
def glyphWordOf (opcodes : List String) : String :=
  (opcodes.map glyphOf).foldl String.append ""

/-- Conventional register from an opcode-name sequence. -/
def conventionalRegisterOf (opcodes : List String) : List ConventionalExpr :=
  opcodes.map conventionalExprOf

end Imscribing
