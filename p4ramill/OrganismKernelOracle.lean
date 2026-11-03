import Init.Paraconsistent
import Lean.Sixteen3

open Lean Paraconsistent

/-! Organism Kernel Oracle: Belnap lattice operations over Sixteen3 masks,
providing the dialetheic truth-value machinery for the organism's decision
procedures. All operations run on Four-valued Belnap logic (N, T, F, B). -/

-- Derived: check if a Sixteen3 state is dialetheic (both true and false)
def isDialetheic (s : Lean.Sixteen3) : Bool :=
  s.hasB

-- Derived: check if a Sixteen3 state is void (neither true nor false)
def isVoid (s : Lean.Sixteen3) : Bool :=
  s.hasN && ¬s.hasT && ¬s.hasF && ¬s.hasB

-- Derived: check if a Sixteen3 state is purely true (T only)
def isTrue (s : Lean.Sixteen3) : Bool :=
  s.hasT && ¬s.hasF && ¬s.hasB && ¬s.hasN

-- Derived: check if a Sixteen3 state is purely false (F only)
def isFalse (s : Lean.Sixteen3) : Bool :=
  s.hasF && ¬s.hasT && ¬s.hasB && ¬s.hasN

-- Derived: check if a Sixteen3 state is contradictory-or-true (has T, possibly B)
def isTrueish (s : Lean.Sixteen3) : Bool :=
  s.hasT || s.hasB

-- Derived: check if a Sixteen3 state is contradictory-or-false (has F, possibly B)
def isFalseish (s : Lean.Sixteen3) : Bool :=
  s.hasF || s.hasB

-- Derived: check if a Sixteen3 state is unknown-or-null (has N, possibly B)
def isNullish (s : Lean.Sixteen3) : Bool :=
  s.hasN || s.hasB

-- Derived: Belnap negation on Sixteen3 (swap T and F)
def negateOf (s : Lean.Sixteen3) : Lean.Sixteen3 :=
  { hasN := s.hasN, hasT := s.hasF, hasF := s.hasT, hasB := s.hasB }

-- Derived: classify a Sixteen3 state into one of 5 Belnap classes
def classifyState (s : Lean.Sixteen3) : String :=
  if isVoid s then "VOID"
  else if isTrue s then "TRUE"
  else if isFalse s then "FALSE"
  else if isDialetheic s then "DIALETHEIC"
  else "MIXED"

-- Derived: compute the Belnap meet of two Sixteen3 states (componentwise min)
def meetOf (a b : Lean.Sixteen3) : Lean.Sixteen3 :=
  { hasN := a.hasN && b.hasN, hasT := a.hasT && b.hasT,
    hasF := a.hasF && b.hasF, hasB := a.hasB && b.hasB }

-- Derived: compute the Belnap join of two Sixteen3 states (componentwise max)
def joinOf (a b : Lean.Sixteen3) : Lean.Sixteen3 :=
  { hasN := a.hasN || b.hasN, hasT := a.hasT || b.hasT,
    hasF := a.hasF || b.hasF, hasB := a.hasB || b.hasB }

-- Derived: check if two Sixteen3 states are Belnap-equivalent
def belnapEq (a b : Lean.Sixteen3) : Bool :=
  a = b
