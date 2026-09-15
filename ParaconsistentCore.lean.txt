/-
  ParaconsistentCore.lean
  Self-contained Belnap 4-valued paraconsistent logic.
  Compatible with vanilla Lean 4.30.0.
-/

/-- The Belnap four-valued logic type for paraconsistent reasoning. -/
inductive Belnap : Type where
  | N | T | F | B
  deriving DecidableEq, Repr, Inhabited

namespace Belnap

def band (a b : Belnap) : Belnap :=
  match a, b with
  | .F, _ | _, .F => .F
  | .N, _ | _, .N => .N
  | .B, _ | _, .B => .B
  | .T, .T => .T

def bor (a b : Belnap) : Belnap :=
  match a, b with
  | .T, _ | _, .T => .T
  | .B, _ | _, .B => .B
  | .N, _ | _, .N => .N
  | .F, .F => .F

def bnot : Belnap → Belnap
  | .N => .N
  | .T => .F
  | .F => .T
  | .B => .B

end Belnap
