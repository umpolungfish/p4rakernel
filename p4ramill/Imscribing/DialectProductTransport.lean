import Mathlib

namespace Imscribing.DialectProductTransport

/-- Coefficients supplied by an executing dialect operator. -/
structure Frame (R : Type*) where
  a : R
  b : R
  c : R
  d : R

variable {R : Type*} [CommRing R]

def determinant (m : Frame R) : R := m.a * m.d - m.b * m.c

def act (m : Frame R) (x : R × R) : R × R :=
  (m.a * x.1 + m.b * x.2, m.c * x.1 + m.d * x.2)

def adjugate (m : Frame R) : Frame R := ⟨m.d, -m.b, -m.c, m.a⟩

/-- The next operator acts on the already carried frame. -/
def compose (m k : Frame R) : Frame R :=
  ⟨m.a * k.a + m.b * k.c, m.a * k.b + m.b * k.d,
   m.c * k.a + m.d * k.c, m.c * k.b + m.d * k.d⟩

theorem act_compose (m k : Frame R) (x : R × R) :
    act (compose m k) x = act m (act k x) := by
  apply Prod.ext <;> simp only [act, compose] <;> ring

theorem determinant_compose (m k : Frame R) :
    determinant (compose m k) = determinant m * determinant k := by
  simp only [determinant, compose]
  ring

theorem adjugate_return (m : Frame R) (x : R × R) :
    act (adjugate m) (act m x) = (determinant m * x.1, determinant m * x.2) := by
  apply Prod.ext <;> simp only [act, adjugate, determinant] <;> ring

/-- Both factor arms and their source residual transform together. -/
theorem residual_transport (m : Frame R) (x : R × R) (n : R) :
    (act (adjugate m) (act m x)).1 * (act (adjugate m) (act m x)).2 -
        determinant m ^ 2 * n =
      determinant m ^ 2 * (x.1 * x.2 - n) := by
  rw [adjugate_return]
  ring

def recover (m : Frame R) (inverse : R) (x : R × R) : R × R :=
  (inverse * (act (adjugate m) (act m x)).1,
   inverse * (act (adjugate m) (act m x)).2)

theorem recover_unit (m : Frame R) (inverse : R) (x : R × R)
    (h : inverse * determinant m = 1) : recover m inverse x = x := by
  unfold recover
  rw [adjugate_return]
  apply Prod.ext <;> simp only [← mul_assoc, h, one_mul]

theorem source_boundary_return (m : Frame R) (inverse : R) (x : R × R) (n : R)
    (h : inverse * determinant m = 1) :
    (recover m inverse x).1 * (recover m inverse x).2 = n ↔ x.1 * x.2 = n := by
  rw [recover_unit m inverse x h]

#print axioms act_compose
#print axioms determinant_compose
#print axioms residual_transport
#print axioms recover_unit
#print axioms source_boundary_return

/-- A promotion displacement acts on the retained operand in the same ring.
    The displacement and dialect label are retained for the inverse return. -/
structure PromotionPoint (R : Type*) where
  dialect : Nat
  axis : Fin 12
  displacement : R
  operand : R

def promotePoint (dialect : Nat) (axis : Fin 12) (shift point : R) : PromotionPoint R :=
  ⟨dialect, axis, shift, point + shift⟩

def returnPoint (point : PromotionPoint R) : R := point.operand - point.displacement

theorem promotion_point_return (dialect : Nat) (axis : Fin 12) (shift point : R) :
    returnPoint (promotePoint dialect axis shift point) = point := by
  simp [returnPoint, promotePoint]

theorem promotion_frame_return (m : Frame R) (inverse : R)
    (dialect : Nat) (axis : Fin 12) (shift point other : R)
    (h : inverse * determinant m = 1) :
    returnPoint { promotePoint dialect axis shift point with
      operand := (recover m inverse ((promotePoint dialect axis shift point).operand, other)).1 }
      = point := by
  rw [recover_unit m inverse _ h]
  exact promotion_point_return dialect axis shift point

#print axioms promotion_point_return
#print axioms promotion_frame_return

namespace SourceSupport

/-- Low coefficient first, matching the ordered source numeral. -/
def evaluate : List R → R → R
  | [], _ => 0
  | a :: tail, x => a + x * evaluate tail x

def divided : List R → R → R → R
  | [], _, _ => 0
  | _ :: tail, x, y => evaluate tail x + y * divided tail x y

def derivative : List R → R → R
  | [], _ => 0
  | _ :: tail, x => evaluate tail x + x * derivative tail x

theorem difference (coefficients : List R) (x y : R) :
    evaluate coefficients x - evaluate coefficients y =
      (x - y) * divided coefficients x y := by
  induction coefficients with
  | nil => simp [evaluate, divided]
  | cons a tail ih =>
    simp only [evaluate, divided]
    calc
      a + x * evaluate tail x - (a + y * evaluate tail y) =
          (x - y) * evaluate tail x + y * (evaluate tail x - evaluate tail y) := by ring
      _ = (x - y) * (evaluate tail x + y * divided tail x y) := by rw [ih]; ring

theorem diagonal_derivative (coefficients : List R) (x : R) :
    divided coefficients x x = derivative coefficients x := by
  induction coefficients <;> simp_all [divided, derivative]

/-- The source value and the known source point remain in the same equation. -/
theorem source_root_return (coefficients : List R) (x base source : R)
    (h : evaluate coefficients base = source) :
    evaluate coefficients x - source = (x - base) * divided coefficients x base := by
  rw [← h, difference]

theorem newton_correction (coefficients : List R) (x inverse : R)
    (h : inverse * derivative coefficients x = 1) :
    derivative coefficients x *
        (x - (x - evaluate coefficients x * inverse)) = evaluate coefficients x := by
  calc
    _ = evaluate coefficients x * (inverse * derivative coefficients x) := by ring
    _ = evaluate coefficients x := by rw [h]; ring

#print axioms difference
#print axioms diagonal_derivative
#print axioms source_root_return
theorem secant_correction (coefficients : List R) (x y inverse : R)
    (h : inverse * divided coefficients x y = 1) :
    divided coefficients x y *
        (x - (x - evaluate coefficients x * inverse)) = evaluate coefficients x := by
  calc
    _ = evaluate coefficients x * (inverse * divided coefficients x y) := by ring
    _ = evaluate coefficients x := by rw [h]; ring

#print axioms secant_correction
#print axioms newton_correction

end SourceSupport

namespace ParityReturn

variable {Cell : Type*}

def even (word : ℕ → Cell) (i : ℕ) : Cell := word (2 * i)
def odd (word : ℕ → Cell) (i : ℕ) : Cell := word (2 * i + 1)
def interlace (left right : ℕ → Cell) (i : ℕ) : Cell :=
  if i % 2 = 0 then left (i / 2) else right (i / 2)

/-- Both correlated cell arms recover the complete original numeral. -/
theorem split_return (word : ℕ → Cell) : interlace (even word) (odd word) = word := by
  funext i
  simp only [interlace, even, odd]
  split <;> congr 1 <;> omega

#print axioms split_return

end ParityReturn

end Imscribing.DialectProductTransport
