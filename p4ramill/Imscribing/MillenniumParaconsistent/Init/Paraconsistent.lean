/-
  Init/Paraconsistent.lean
  MillenniumParaconsistent — paraconsistent substrate (RECONNECTED)

  This is a faithful local instantiation of the canonical
  p4ramill `Imscribing.Paraconsistent.Belnap` substrate (Belnap FOUR:
  band, bnot, join, meet, designated), re-namespaced to the
  `Paraconsistent` / `Paraconsistent.Belnap` layout the
  MillenniumParaconsistent modules were written against (the
  paraconsistent-kernel fork, where `False.rec` is blocked for empty
  Prop inductives and ex falso is unavailable).

  The lattice tables are copied verbatim from
  /p4rakernel/p4ramill/Imscribing/Paraconsistent/Belnap.lean so the
  dialetheic theorems here agree with the canonical Imscribing kernel.
  `native_decide` is the standard core tactic (no fork required).
-/

namespace Paraconsistent
namespace Belnap

/-- Belnap four-valued logic: N (neither), T (true), F (false), B (both) -/
inductive Belnap : Type where
  | N | T | F | B
  deriving DecidableEq, Repr, Inhabited

/-- Belnap conjunction (truth-functional FDE meet). Canonical table. -/
def band (a b : Belnap) : Belnap :=
  match a, b with
  | .F, _ | _, .F => .F
  | .N, .B | .B, .N => .F
  | .T, x => x
  | x, .T => x
  | .N, .N => .N
  | .B, .B => .B

/-- Belnap disjunction (truth-functional). Canonical table. -/
def bor (a b : Belnap) : Belnap :=
  match a, b with
  | .T, _ | _, .T => .T
  | .N, .B | .B, .N => .T
  | .F, x => x
  | x, .F => x
  | .N, .N => .N
  | .B, .B => .B

/-- Belnap negation: ¬N=N, ¬T=F, ¬F=T, ¬B=B. B is a fixed point. -/
def bnot (a : Belnap) : Belnap :=
  match a with
  | .N => .N | .T => .F | .F => .T | .B => .B

/-- Lattice join in the information order: N ⊑ T ⊑ B, N ⊑ F ⊑ B. -/
def join (a b : Belnap) : Belnap :=
  match a, b with
  | .B, _ | _, .B => .B
  | .N, x | x, .N => x
  | .T, .F | .F, .T => .B
  | .T, .T => .T
  | .F, .F => .F

/-- Lattice meet in the information order. -/
def meet (a b : Belnap) : Belnap :=
  match a, b with
  | .N, _ | _, .N => .N
  | .B, x | x, .B => x
  | .T, .F | .F, .T => .N
  | .T, .T => .T
  | .F, .F => .F

/-- Designated values: T or B count as "true" for paraconsistent consequence. -/
def designated (b : Belnap) : Bool :=
  match b with
  | .T | .B => true | .N | .F => false

/-- No explosion: B ∧ ¬B = B (not F). Contradiction is contained. -/
theorem no_explosion : band .B (bnot .B) = .B := rfl

end Belnap
end Paraconsistent
