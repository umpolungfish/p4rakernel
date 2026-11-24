import Imscribing.Paraconsistent.SixteenThreeTrilattice

/-! Source paths retain their boundary register and ordered component ancestry.
These are laws of the executing path carrier, not a completed folding theorem.
-/
namespace Imscribing.Biochem.PeptideSourcePaths

abbrev Boundary := Nat × Reg16_3

def reverseBoundary (b : Boundary) : Boundary := (b.1, Reg16_3.invol b.2)

theorem reverseBoundary_twice (b : Boundary) :
    reverseBoundary (reverseBoundary b) = b := by
  cases b
  simp [reverseBoundary, Reg16_3.invol_involutive]

structure SourcePath where
  source : Boundary
  target : Boundary
  steps : List (Nat × Bool)
  deriving DecidableEq

def Composable (p q : SourcePath) : Prop := p.target = q.source

def compose (p q : SourcePath) : SourcePath :=
  ⟨p.source, q.target, p.steps ++ q.steps⟩

def identity (b : Boundary) : SourcePath := ⟨b, b, []⟩

def flipStep (s : Nat × Bool) : Nat × Bool := (s.1, !s.2)

def dagger (p : SourcePath) : SourcePath :=
  ⟨reverseBoundary p.target, reverseBoundary p.source,
   p.steps.reverse.map flipStep⟩

theorem compose_associative (p q r : SourcePath) :
    compose (compose p q) r = compose p (compose q r) := by
  simp [compose, List.append_assoc]

theorem identity_left (p : SourcePath) : compose (identity p.source) p = p := by
  cases p
  simp [compose, identity]

theorem identity_right (p : SourcePath) : compose p (identity p.target) = p := by
  cases p
  simp [compose, identity]

theorem composable_dagger {p q : SourcePath} (h : Composable p q) :
    Composable (dagger q) (dagger p) := by
  exact congrArg reverseBoundary h.symm

theorem flipStep_twice (s : Nat × Bool) : flipStep (flipStep s) = s := by
  cases s with
  | mk id direction => cases direction <;> rfl

theorem dagger_twice (p : SourcePath) : dagger (dagger p) = p := by
  cases p with
  | mk source target steps =>
    simp [dagger, reverseBoundary_twice, List.map_reverse, List.map_map,
      Function.comp_def, flipStep_twice]

theorem dagger_compose (p q : SourcePath) :
    dagger (compose p q) = compose (dagger q) (dagger p) := by
  simp [dagger, compose, List.reverse_append, List.map_append]

-- A path with no active register lanes remains a source path. Its existence
-- is carried independently of the register annotation.
structure AnnotatedPath where
  path : SourcePath
  reg : Reg16_3

def forgetRegister (p : AnnotatedPath) : SourcePath := p.path

theorem annotation_does_not_erase_path (p : SourcePath) (r : Reg16_3) :
    forgetRegister ⟨p, r⟩ = p := rfl

#print axioms compose_associative
#print axioms dagger_twice
#print axioms dagger_compose

end Imscribing.Biochem.PeptideSourcePaths
