import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Imscribing.TrilatticeYM



inductive Belnap4 : Type
  | N | F | T | B
  deriving DecidableEq, Repr

instance : Fintype Belnap4 where
  elems := {.N, .F, .T, .B}
  complete := by intro x; cases x <;> decide

theorem card_belnap4 : Fintype.card Belnap4 = 4 := rfl

abbrev Sixteen3 : Type := Belnap4 → Bool

theorem card_sixteen3 : Fintype.card Sixteen3 = 16 := by
  simp [Sixteen3, Fintype.card_fun, card_belnap4]

@[inline] def impBool (a b : Bool) : Bool := (!a) || b

private lemma imp_eq_of {a b : Bool} (h1 : impBool a b = true) (h2 : impBool b a = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [impBool]

def le_i (x y : Sixteen3) : Bool :=
  (impBool (x .N) (y .N)) && (impBool (x .F) (y .F)) &&
  (impBool (x .T) (y .T)) && (impBool (x .B) (y .B))

def le_t (x y : Sixteen3) : Bool :=
  (impBool (x .T) (y .T)) && (impBool (x .B) (y .B)) &&
  (impBool (y .N) (x .N)) && (impBool (y .F) (x .F))

def le_f (x y : Sixteen3) : Bool :=
  (impBool (x .F) (y .F)) && (impBool (x .B) (y .B)) &&
  (impBool (y .N) (x .N)) && (impBool (y .T) (x .T))

def sVoid : Sixteen3 := fun _ => false
def sNeither : Sixteen3 := fun b => b == .N
def sFalse : Sixteen3 := fun b => b == .F
def sTrue : Sixteen3 := fun b => b == .T
def sBoth : Sixteen3 := fun b => b == .B
def sGlut : Sixteen3 := fun b => (b == .T) || (b == .F)
def sTopI : Sixteen3 := fun _ => true

theorem generalized_values_distinct :
    sVoid ≠ sTrue ∧ sVoid ≠ sFalse ∧ sVoid ≠ sBoth ∧
    sTrue ≠ sFalse ∧ sTrue ≠ sBoth ∧ sFalse ≠ sBoth ∧
    sGlut ≠ sVoid ∧ sGlut ≠ sTopI := by decide

theorem le_i_refl : ∀ x : Sixteen3, le_i x x = true := by decide

theorem le_i_antisymm : ∀ x y : Sixteen3, le_i x y = true → le_i y x = true → x = y := by
  intro x y h1 h2
  simp only [le_i, Bool.and_eq_true] at h1 h2
  funext b
  cases b
  · exact imp_eq_of h1.1.1.1 h2.1.1.1
  · exact imp_eq_of h1.1.1.2 h2.1.1.2
  · exact imp_eq_of h1.1.2 h2.1.2
  · exact imp_eq_of h1.2 h2.2

theorem le_i_trans : ∀ x y z : Sixteen3, le_i x y = true → le_i y z = true → le_i x z = true := by
  decide

theorem le_t_refl : ∀ x : Sixteen3, le_t x x = true := by decide
theorem le_f_refl : ∀ x : Sixteen3, le_f x x = true := by decide

theorem orders_mutually_distinct :
    le_t ≠ le_i ∧ le_f ≠ le_i ∧ le_t ≠ le_f := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : le_t sFalse sVoid = true := by decide
    have h2 : le_i sFalse sVoid = false := by decide
    have h_app := congrFun (congrFun h sFalse) sVoid
    rw [h1, h2] at h_app
    nomatch h_app
  · intro h
    have h1 : le_f sTrue sVoid = true := by decide
    have h2 : le_i sTrue sVoid = false := by decide
    have h_app := congrFun (congrFun h sTrue) sVoid
    rw [h1, h2] at h_app
    nomatch h_app
  · intro h
    have h1 : le_t sFalse sTrue = true := by decide
    have h2 : le_f sFalse sTrue = false := by decide
    have h_app := congrFun (congrFun h sFalse) sTrue
    rw [h1, h2] at h_app
    nomatch h_app

structure ReentrantTrilattice where
  S : Type
  Sub : Type
  le_t : S → S → Prop
  le_f : S → S → Prop
  le_i : S → S → Prop
  le_i_refl : ∀ x, le_i x x
  le_i_antisymm : ∀ x y, le_i x y → le_i y x → x = y
  le_i_trans : ∀ x y z, le_i x y → le_i y z → le_i x z
  le_t_refl : ∀ x, le_t x x
  le_f_refl : ∀ x, le_f x x
  orders_distinct : le_t ≠ le_i ∧ le_f ≠ le_i ∧ le_t ≠ le_f
  void : S
  topI : S
  topI_max : ∀ x, le_i x topI
  incCode : S
  seq : S → S → S
  Inc : S → S
  R : S → S
  μ : S → Sub
  δ : Sub → S
  W : S → S
  distinction_axiom : Inc incCode ≠ void
  noncomm_reentry : ∃ A B : S, Inc (seq A B) ≠ Inc (seq B A)
  reentry_idempotent : ∀ x, R (R x) = R x
  fixed_point_mandate : ∃ x, Inc x = x
  totality_surjective : Function.Surjective μ
  totality_not_injective : ¬ Function.Injective μ
  core_law : ∀ s, μ (δ s) = s
  walk_mono : ∀ x, le_i x (W x)
  walk_strict : ∀ x, x ≠ topI → x ≠ W x

namespace ReentrantTrilattice

theorem walk_iter_le (M : ReentrantTrilattice) :
    ∀ (n : ℕ) (x : M.S), M.le_i x (M.W^[n] x)
  | 0, x => M.le_i_refl x
  | n + 1, x => by
      rw [Function.iterate_succ_apply']
      exact M.le_i_trans x (M.W^[n] x) (M.W (M.W^[n] x))
        (walk_iter_le M n x) (M.walk_mono (M.W^[n] x))

theorem walk_step_monotone (M : ReentrantTrilattice) {m n : ℕ} (hmn : m ≤ n) (x : M.S) :
    M.le_i (M.W^[m] x) (M.W^[n] x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, Function.iterate_add_apply]
  exact walk_iter_le M k (M.W^[m] x)

theorem walk_fixed_at_top (M : ReentrantTrilattice) : M.W M.topI = M.topI :=
  M.le_i_antisymm (M.W M.topI) M.topI (M.topI_max _) (M.walk_mono M.topI)

end ReentrantTrilattice

def canonicalWalk (x : Sixteen3) : Sixteen3 :=
  if !(x .N) then fun b => if b == .N then true else x b
  else if !(x .F) then fun b => if b == .F then true else x b
  else if !(x .T) then fun b => if b == .T then true else x b
  else if !(x .B) then fun b => if b == .B then true else x b
  else x

def canonicalMu (x : Sixteen3) : Belnap4 :=
  if x .B then .B
  else if x .T then .T
  else if x .F then .F
  else .N

def canonicalDelta (b : Belnap4) : Sixteen3 := fun b' => decide (b = b')
def canonicalJoinI (x y : Sixteen3) : Sixteen3 := fun b => x b || y b
def canonicalSeq (x y : Sixteen3) : Sixteen3 := if x .B then y else sTopI
def canonicalInc (x : Sixteen3) : Sixteen3 := canonicalJoinI x sBoth
def canonicalR (x : Sixteen3) : Sixteen3 := canonicalJoinI x sBoth

private theorem canonicalWalk_mono_all : ∀ x : Sixteen3, le_i x (canonicalWalk x) = true := by
  decide

private theorem canonicalWalk_fixed_top : ∀ x : Sixteen3, x = canonicalWalk x → x = sTopI := by
  decide

def canonicalSixteen3 : ReentrantTrilattice where
  S := Sixteen3
  Sub := Belnap4
  le_t := fun x y => le_t x y = true
  le_f := fun x y => le_f x y = true
  le_i := fun x y => le_i x y = true
  le_i_refl := le_i_refl
  le_i_antisymm := le_i_antisymm
  le_i_trans := le_i_trans
  le_t_refl := le_t_refl
  le_f_refl := le_f_refl
  orders_distinct := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have h1 : le_t sFalse sVoid = true := by decide
      have h2 : le_i sFalse sVoid = false := by decide
      have h_app := congrFun (congrFun h sFalse) sVoid
      rw [h1, h2] at h_app
      revert h_app; decide
    · intro h
      have h1 : le_f sTrue sVoid = true := by decide
      have h2 : le_i sTrue sVoid = false := by decide
      have h_app := congrFun (congrFun h sTrue) sVoid
      rw [h1, h2] at h_app
      revert h_app; decide
    · intro h
      have h1 : le_t sFalse sTrue = true := by decide
      have h2 : le_f sFalse sTrue = false := by decide
      have h_app := congrFun (congrFun h sFalse) sTrue
      rw [h1, h2] at h_app
      revert h_app; decide
  void := sVoid
  topI := sTopI
  topI_max := by decide
  incCode := sBoth
  seq := canonicalSeq
  Inc := canonicalInc
  R := canonicalR
  μ := canonicalMu
  δ := canonicalDelta
  W := canonicalWalk
  distinction_axiom := by decide
  noncomm_reentry := ⟨sBoth, sFalse, by decide⟩
  reentry_idempotent := by
    intro x; funext b; cases b <;> simp [canonicalR, canonicalJoinI, sBoth]
  fixed_point_mandate := ⟨sTopI, by decide⟩
  totality_surjective := fun b => ⟨canonicalDelta b, by cases b <;> decide⟩
  totality_not_injective := by
    intro hinj
    have h : canonicalMu sVoid = canonicalMu (canonicalDelta .N) := by decide
    have eq := hinj h
    revert eq; decide
  core_law := fun b => by cases b <;> decide
  walk_mono := fun x => canonicalWalk_mono_all x
  walk_strict := fun x hx hwx => hx (canonicalWalk_fixed_top x hwx)

section LinearSplit

open Matrix

variable {N n : ℕ}

theorem split_proj_idempotent
    (D : Matrix (Fin N) (Fin n) ℂ) (μ : Matrix (Fin n) (Fin N) ℂ)
    (hμD : μ * D = 1) :
    (D * μ) * (D * μ) = D * μ := by
  calc (D * μ) * (D * μ)
      = D * (μ * D) * μ := by simp only [Matrix.mul_assoc]
    _ = D * (1 : Matrix (Fin n) (Fin n) ℂ) * μ := by rw [hμD]
    _ = D * μ := by simp only [Matrix.mul_one]

theorem split_direct_decomp
    (D : Matrix (Fin N) (Fin n) ℂ) (μ : Matrix (Fin n) (Fin N) ℂ)
    (hμD : μ * D = 1) (v : Fin N → ℂ) :
    (D * μ) *ᵥ v + (1 - D * μ) *ᵥ v = v ∧ μ *ᵥ ((1 - D * μ) *ᵥ v) = 0 := by
  constructor
  · simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  · calc μ *ᵥ ((1 - D * μ) *ᵥ v)
        = (μ * (1 - D * μ)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = (μ - (μ * D) * μ) *ᵥ v := by simp [Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by simp [hμD]

theorem metric_compat_iff
    (D : Matrix (Fin N) (Fin n) ℂ) (μ : Matrix (Fin n) (Fin N) ℂ)
    (G : Matrix (Fin N) (Fin N) ℂ)
    (hμD : μ * D = 1) (hG : G.IsHermitian) :
    G * (D * μ) = (D * μ)ᴴ * G ↔ (Dᴴ * G * D) * μ = Dᴴ * G := by
  set P := D * μ
  constructor
  · intro hGP
    calc (Dᴴ * G * D) * μ
        = Dᴴ * (G * P) := by simp [P, Matrix.mul_assoc]
      _ = Dᴴ * (Pᴴ * G) := by rw [hGP]
      _ = (P * D)ᴴ * G := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (D * (μ * D))ᴴ * G := by simp [P, Matrix.mul_assoc]
      _ = Dᴴ * G := by simp [hμD]
  · intro hnorm
    have hPG : Pᴴ * G = Pᴴ * G * P := by
      calc Pᴴ * G
          = μᴴ * (Dᴴ * G) := by simp [P, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = μᴴ * ((Dᴴ * G * D) * μ) := by rw [hnorm]
        _ = (D * μ)ᴴ * G * (D * μ) := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Pᴴ * G * P := rfl
    have hsym : (Pᴴ * G * P)ᴴ = Pᴴ * G * P := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hG.eq, Matrix.conjTranspose_conjTranspose]
    calc G * P
        = Gᴴ * P := by rw [hG.eq]
      _ = (Pᴴ * G)ᴴ := by simp [Matrix.conjTranspose_mul]
      _ = (Pᴴ * G * P)ᴴ := by rw [← hPG]
      _ = Pᴴ * G * P := hsym
      _ = Pᴴ * G := hPG.symm

end LinearSplit

end Imscribing.TrilatticeYM
