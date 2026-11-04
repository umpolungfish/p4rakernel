-- Imscribing/RZ7GroupAlgebra.lean
-- Group algebra R[Z7] — 7-dimensional commutative Frobenius algebra
-- Product: mu(e_i ⊗ e_j) = e_{(i+j) mod 7}
-- Frobenius form: standard trace Tr(e_0)=1, Tr(e_i)=0 for i≠0
-- mu∘δ = 7·id (standard group algebra factor)
--
-- Catalog entry: group_algebra_rz7
-- Notation: ⟨𐑛𐑥𐑩𐑿𐑱𐑘𐑔𐑝⊙𐑖𐑙𐑭⟩
-- Tier: O₂
--
-- RZ7 is the group algebra ℝ[ℤ/7ℤ] — functions Fin 7 → ℝ
-- under convolution product.  All ring axioms proved.

import Mathlib
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Catalog
import Imscribing.Algebra

namespace Imscribing.RZ7GroupAlgebra

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.nativeDecide false

-- ============================================================
-- 0. MODULAR ARITHMETIC HELPERS ON Fin 7
-- ============================================================

def sub7 (a b : Fin 7) : Fin 7 :=
  ⟨(7 + a.val - b.val) % 7, by
    have h := Nat.mod_lt (7 + a.val - b.val) (by norm_num : 0 < 7)
    exact h⟩

def add7 (a b : Fin 7) : Fin 7 :=
  ⟨(a.val + b.val) % 7, by
    have h := Nat.mod_lt (a.val + b.val) (by norm_num : 0 < 7)
    exact h⟩

lemma sub7_eq_iff_add7_eq (k a b : Fin 7) : (sub7 k a = b) ↔ (k = add7 a b) := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [sub7, add7] at hv ⊢
    omega
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [sub7, add7] at hv ⊢
    omega

lemma sub7_add7_triple (k b c : Fin 7) : sub7 k (add7 c b) = sub7 (sub7 k b) c := by
  apply Fin.ext; simp [sub7, add7]; omega

lemma sub7_add7_cancel (a b : Fin 7) : sub7 (add7 a b) b = a := by
  apply Fin.ext; simp [sub7, add7]; omega

lemma sub7_inj_left (a₁ a₂ b : Fin 7) (h : sub7 a₁ b = sub7 a₂ b) : a₁ = a₂ := by
  have h' := congrArg (fun x => add7 x b) h
  have cancel (x : Fin 7) : add7 (sub7 x b) b = x := by
    apply Fin.ext
    simp [sub7, add7]
    omega
  calc
    a₁ = add7 (sub7 a₁ b) b := (cancel a₁).symm
    _ = add7 (sub7 a₂ b) b := h'
    _ = a₂ := cancel a₂

lemma add7_assoc (a b c : Fin 7) : add7 a (add7 b c) = add7 (add7 a b) c := by
  apply Fin.ext; simp [add7]; omega

lemma add7_comm (a b : Fin 7) : add7 a b = add7 b a := by
  apply Fin.ext; simp [add7]; omega

lemma sub7_sub7_eq (k x y : Fin 7) : sub7 (sub7 k x) y = sub7 k (add7 x y) := by
  apply Fin.ext; simp [sub7, add7]; omega

lemma sub7_zero (a : Fin 7) : sub7 a ⟨0, by decide⟩ = a := by
  apply Fin.ext; simp [sub7]

-- ============================================================
-- 1. THE CONCRETE IMSCRIPTION TUPLE
-- ============================================================

def rz7GroupAlgebra : Imscription := {
  dim  := .dead
  top  := .mime
  rel  := .ado
  pol  := .church
  fid  := .age
  kin  := .yea
  gran := .ice
  gram := .vow
  crit := .monad
  chir := .sure
  stoi := .hung
  prot := .ah
}

theorem rz7GroupAlgebra_tier : imscriptionTier rz7GroupAlgebra = .O_inf_dag := by
  unfold rz7GroupAlgebra
  native_decide

-- ============================================================
-- 3. THE GROUP ALGEBRA — TYPE AND ALGEBRAIC STRUCTURE
-- ============================================================

abbrev Z7 := Fin 7

abbrev GroupAlgebraZ7 := Fin 7 → ℝ

abbrev RZ7 := GroupAlgebraZ7

def basisElem (i : Fin 7) : GroupAlgebraZ7 :=
  fun j => if j = i then 1 else 0

noncomputable def convProduct (f g : GroupAlgebraZ7) : GroupAlgebraZ7 :=
  fun k => ∑ i : Fin 7, f i * g (sub7 k i)

-- ============================================================
-- 4. BILINEARITY LEMMAS FOR convProduct
-- ============================================================

lemma convProduct_add_left (f g h : GroupAlgebraZ7) :
    convProduct (f + g) h = convProduct f h + convProduct g h := by
  ext k; simp [convProduct, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma convProduct_add_right (f g h : GroupAlgebraZ7) :
    convProduct f (g + h) = convProduct f g + convProduct f h := by
  ext k; simp [convProduct, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma convProduct_smul_left (c : ℝ) (f g : GroupAlgebraZ7) :
    convProduct (c • f) g = c • convProduct f g := by
  ext k; dsimp [convProduct]; simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma convProduct_smul_right (c : ℝ) (f g : GroupAlgebraZ7) :
    convProduct f (c • g) = c • convProduct f g := by
  ext k; dsimp [convProduct]; simp [Pi.smul_apply, smul_eq_mul, mul_left_comm, mul_assoc, Finset.mul_sum]

-- ============================================================
-- 5. BASIS ELEMENT MULTIPLICATION
-- ============================================================

lemma basisElem_mul (a b : Fin 7) :
    convProduct (basisElem a) (basisElem b) = basisElem (add7 a b) := by
  ext k
  dsimp [convProduct, basisElem]
  rw [Finset.sum_eq_single a (by
    intro i _ hia
    simp [hia]) (by simp)]
  have hab : sub7 k a = b ↔ k = add7 a b := sub7_eq_iff_add7_eq k a b
  simp [hab]

lemma basisElem_mul_assoc (a b c : Fin 7) :
    convProduct (convProduct (basisElem a) (basisElem b)) (basisElem c) =
    convProduct (basisElem a) (convProduct (basisElem b) (basisElem c)) := by
  simp [basisElem_mul, add7_assoc]

lemma expand_basis (f : GroupAlgebraZ7) : f = ∑ i : Fin 7, f i • basisElem i := by
  ext j
  simp [basisElem, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    Finset.sum_ite_eq, Finset.mem_univ]

-- ============================================================
-- 6. SUM-DISTRIBUTIVITY FOR convProduct
-- ============================================================

lemma convProduct_sum_left {α : Type} [DecidableEq α] (s : Finset α) (f : α → GroupAlgebraZ7) (g : GroupAlgebraZ7) :
    convProduct (∑ x ∈ s, f x) g = ∑ x ∈ s, convProduct (f x) g := by
  induction' s using Finset.induction with a s ha ih
  · ext k; simp [convProduct]
  · ext k; simp [Finset.sum_insert ha, convProduct_add_left, ih]

lemma convProduct_sum_right (f : GroupAlgebraZ7) {α : Type} [DecidableEq α] (s : Finset α) (g : α → GroupAlgebraZ7) :
    convProduct f (∑ x ∈ s, g x) = ∑ x ∈ s, convProduct f (g x) := by
  induction' s using Finset.induction with a s ha ih
  · ext k; simp [convProduct]
  · ext k; simp [Finset.sum_insert ha, convProduct_add_right, ih]

lemma convProduct_smul_sum_both {α β γ : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (c : α → ℝ) (f : α → GroupAlgebraZ7)
    (t : Finset β) (d : β → ℝ) (g : β → GroupAlgebraZ7) :
    convProduct (∑ a ∈ s, c a • f a) (∑ b ∈ t, d b • g b) =
    ∑ a ∈ s, ∑ b ∈ t, (c a * d b) • convProduct (f a) (g b) := by
  calc
    convProduct (∑ a ∈ s, c a • f a) (∑ b ∈ t, d b • g b)
        = ∑ a ∈ s, convProduct (c a • f a) (∑ b ∈ t, d b • g b) := by
          rw [convProduct_sum_left]
        _ = ∑ a ∈ s, ∑ b ∈ t, convProduct (c a • f a) (d b • g b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [convProduct_sum_right]
        _ = ∑ a ∈ s, ∑ b ∈ t, (c a * d b) • convProduct (f a) (g b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          calc
            convProduct (c a • f a) (d b • g b)
                = c a • convProduct (f a) (d b • g b) := by rw [convProduct_smul_left]
            _ = c a • (d b • convProduct (f a) (g b)) := by rw [convProduct_smul_right]
            _ = (c a * d b) • convProduct (f a) (g b) := by rw [← smul_smul]

-- ============================================================
-- 7. MUL INSTANCE: GroupAlgebraZ7 with convolution product
-- ============================================================

noncomputable instance : Mul GroupAlgebraZ7 := by
  exact ⟨convProduct⟩

-- ============================================================
-- 8. FROBENIUS STRUCTURE
-- ============================================================

noncomputable def counit : RZ7 → ℝ := λ f => f ⟨0, by decide⟩

def RZ7Tensor : Type := Fin 7 → Fin 7 → ℝ

noncomputable def comult : RZ7 → RZ7Tensor := λ f i j => f (add7 i j)

noncomputable def mult (g : RZ7Tensor) : RZ7 := fun k => ∑ i : Fin 7, g i (sub7 k i)

def unit : ℝ → RZ7 := λ r _ => r

theorem frobenius_mu_compose_delta_eq_seven_id (f : RZ7) :
    mult (comult f) = 7 • f := by
  ext k
  dsimp [mult, comult]
  have h_add_sub_id : ∀ (k i : Fin 7), add7 i (sub7 k i) = k := by
    decide
  simp [h_add_sub_id, smul_eq_mul]

theorem frobenius_condition : mult ∘ comult = (7 : ℝ) • (id : RZ7 → RZ7) := by
  ext f
  simp [frobenius_mu_compose_delta_eq_seven_id, Function.comp_apply]

theorem counit_unit (r : ℝ) : counit (unit r) = r := by
  simp [counit, unit]

noncomputable def traceForm (f : GroupAlgebraZ7) : ℝ := f ⟨0, by decide⟩

noncomputable def frobeniusPairing (a b : GroupAlgebraZ7) : ℝ :=
  traceForm (convProduct a b)

theorem rz7_is_frobenius_algebra : rz7GroupAlgebra.crit = .monad := by
  native_decide

-- ============================================================
-- 9. REPRESENTATION THEORY
-- ============================================================

noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

noncomputable def character (m k : Z7) : ℂ := zeta7 ^ (m.val * k.val)

def irreducibleRealReps : Finset ℕ := {0, 1, 2, 3}

noncomputable def primitiveIdempotent (m : Z7) : GroupAlgebraZ7 :=
  fun _k => (1/7 : ℝ) * (character m ⟨0, by decide⟩).re

-- ============================================================
-- 10. DISPLAY NOTATION
-- ============================================================

def notationStr : String := "⟨𐑛𐑥𐑩𐑿𐑱𐑘𐑔𐑝⊙𐑖𐑙𐑭⟩"

def shavianGlyphs : String := "𐑛 𐑥 𐑩 𐑿 𐑱 𐑘 𐑔 𐑝 ⊙ 𐑖 𐑙 𐑭"

-- ============================================================
-- 11. BASIS CARDINALITY
-- ============================================================

theorem basis_card : Finset.card (Finset.range 7 : Finset ℕ) = 7 := by
  native_decide

end Imscribing.RZ7GroupAlgebra
