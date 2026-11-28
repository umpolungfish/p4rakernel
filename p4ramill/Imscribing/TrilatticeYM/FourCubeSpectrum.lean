import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option maxHeartbeats 800000
set_option maxRecDepth 200000


/-!
# 4-Cube Quaternion Reduction, `4^r → 2^r` Collapse, Trine Identities, and All-`k` Spectral Bounds (§§437–446)

Formalizes:
1. Quaternion/Pauli reduction `B₀..B₄ ↦ (B_u = 0; B_σ, B_{t₁}, B_{t₂}, B_v)` and bistochasticity.
2. Exact unitary isomorphism `Wiso r : (u^⊥)^{⊗ r} → M_{2^r}(ℂ)` and `4^r → 2^r` tensor collapse.
3. Exact Bell-projector gluing identity `∑_a B_a ⊗ B_a = |Φ⁺⟩⟨Φ⁺|` across shared `j = 1/2` edges.
4. Planar `120°` trine identities on `ℂ²_mult` (`§439`).
5. Exact spectral comparison bounds (`k = 28` single-face exceedance and `k = 0` global bounds).
-/

namespace Imscribing.TrilatticeYM



open Matrix

noncomputable def Bmat : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => !![0, Real.sqrt 2 / 4; -Real.sqrt 2 / 4, 0]
  | 1 => !![0, Real.sqrt 6 / 4; Real.sqrt 6 / 12, 0]
  | 2 => !![-Real.sqrt 2 / 4, 0; -Real.sqrt 6 / 6, Real.sqrt 2 / 4]
  | 3 => !![Real.sqrt 2 / 4, 0; -Real.sqrt 6 / 6, -Real.sqrt 2 / 4]
  | 4 => !![1 / 2, 0; 0, 1 / 2]

private lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma sqrt6_eq : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]

theorem Bmat_bistochastic :
    (∑ α : Fin 5, (Bmat α)ᵀ * Bmat α = 1) ∧
    (∑ α : Fin 5, Bmat α * (Bmat α)ᵀ = 1) := by
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Bmat, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.one_apply, Fin.sum_univ_five, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue, Fin.reduceFinMk] <;>
      norm_num <;>
      (try rw [sqrt6_eq]) <;>
      ring_nf <;>
      simp only [sqrt2_sq, sqrt3_sq] <;>
      norm_num

theorem Bmat_u_zero :
    Real.sqrt 3 • Bmat 0 - Bmat 1 - Bmat 2 - Bmat 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Bmat, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.reduceFinMk] <;>
    (try rw [sqrt6_eq]) <;>
    ring_nf

noncomputable def Bcomp : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => !![1 / 2, 0; 0, 1 / 2]
  | 1 => !![1 / 4, Real.sqrt 3 / 4; Real.sqrt 3 / 4, -1 / 4]
  | 2 => !![-Real.sqrt 3 / 4, 1 / 4; 1 / 4, Real.sqrt 3 / 4]
  | 3 => !![0, 1 / 2; -1 / 2, 0]

theorem Bcomp_from_Bmat :
    Bcomp 0 = Bmat 4 ∧
    Real.sqrt 2 • Bcomp 1 = Bmat 1 - Bmat 2 ∧
    Real.sqrt 6 • Bcomp 2 = Bmat 1 + Bmat 2 - (2 : ℝ) • Bmat 3 ∧
    Real.sqrt 6 • Bcomp 3 = Real.sqrt 3 • Bmat 0 + Bmat 1 + Bmat 2 + Bmat 3 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Bcomp, Bmat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Fin.reduceFinMk] <;>
      (try rw [sqrt6_eq]) <;>
      ring_nf <;>
      simp only [sqrt2_sq, sqrt3_sq] <;>
      ring

theorem Bcomp_hs_ortho (a b : Fin 4) :
    (Bcomp a * (Bcomp b)ᵀ).trace = if a = b then (1 : ℝ) / 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp only [Bcomp, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] <;>
    norm_num <;>
    ring_nf <;>
    simp only [sqrt3_sq] <;>
    norm_num

theorem Bcomp_sum_ortho (a b : Fin 4) :
    ∑ f : Fin 2, ∑ g : Fin 2, Bcomp a f g * Bcomp b f g =
      if a = b then (1 : ℝ) / 2 else 0 := by
  have h := Bcomp_hs_ortho a b
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, add_assoc] using h

theorem Bcomp_glued_bell_projector (i j k l : Fin 2) :
    ∑ a : Fin 4, Bcomp a i j * Bcomp a k l =
      if i = k ∧ j = l then (1 : ℝ) / 2 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Bcomp, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] <;>
    norm_num <;>
    ring_nf <;>
    simp only [sqrt3_sq] <;>
    norm_num

abbrev MatC (r : ℕ) := Matrix (Fin r → Fin 2) (Fin r → Fin 2) ℂ

noncomputable def Wiso (r : ℕ) : ((Fin r → Fin 4) → ℂ) →ₗ[ℂ] MatC r where
  toFun v g f := ∑ a : Fin r → Fin 4,
    v a * ∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ)
  map_add' v w := by
    ext g f; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext g f; simp [Finset.mul_sum, mul_assoc]

private def prodFunEquiv (r : ℕ) :
    ((Fin r → Fin 2) × (Fin r → Fin 2)) ≃ (Fin r → Fin 2 × Fin 2) where
  toFun p e := (p.1 e, p.2 e)
  invFun q := (fun e => (q e).1, fun e => (q e).2)
  left_inv _ := rfl
  right_inv _ := rfl

private lemma prod_delta_eq {r : ℕ} (a b : Fin r → Fin 4) :
    (∏ e : Fin r, (if a e = b e then (1 : ℂ) else 0)) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab; simp
  · have hne : ∃ e : Fin r, a e ≠ b e := by
      by_contra h; push_neg at h; exact hab (funext h)
    obtain ⟨e, he⟩ := hne
    rw [if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

private lemma sum_star_mul_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) :
    star (∑ a : α, f a) * (∑ b : β, g b) = ∑ a : α, ∑ b : β, star (f a) * g b := by
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _

private lemma sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  let G : α × β → γ × δ → ℂ := fun ab cd => F ab.1 ab.2 cd.1 cd.2
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ ab, ∑ cd, G ab cd := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_prod_type]
  have h2 : (∑ c, ∑ d, ∑ a, ∑ b, F a b c d) = ∑ cd, ∑ ab, G ab cd := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

private lemma bcomp_prod_pair {r : ℕ} (a b : Fin r → Fin 4) (va wb : ℂ)
    (f g : Fin r → Fin 2) :
    star (va * ∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ)) *
      (wb * ∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
    star va * wb *
      ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
        ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ) := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast; exact Real.mul_self_sqrt (by norm_num)
  have hpm :
      (∏ e : Fin r, star ((Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ))) *
      (∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
      ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
        ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [StarMul.star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    linear_combination ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) * ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ) * hsq
  have hsp : star (∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ)) =
      ∏ e : Fin r, star ((Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ)) := by
    simp only [star_prod]
  rw [StarMul.star_mul, hsp]
  linear_combination star va * wb * hpm

theorem Wiso_isometry (r : ℕ) (v w : (Fin r → Fin 4) → ℂ) :
    ((Wiso r v)ᴴ * Wiso r w).trace = star v ⬝ᵥ w := by
  conv_lhs =>
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Wiso, LinearMap.coe_mk, AddHom.coe_mk]
  have hterm (f g : Fin r → Fin 2) :
      star (∑ a : Fin r → Fin 4, v a * ∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ)) *
        (∑ b : Fin r → Fin 4, w b * ∏ e : Fin r, (Real.sqrt 2 : ℂ) * ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
      ∑ a : Fin r → Fin 4, ∑ b : Fin r → Fin 4,
        star (v a) * w b * ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) * ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact bcomp_prod_pair a b (v a) (w b) f g
  simp_rw [hterm]
  have h2 (a b : Fin r → Fin 4) :
      (∑ f : Fin r → Fin 2, ∑ g : Fin r → Fin 2,
        ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
          ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
      if a = b then 1 else 0 := by
    have hprod_sum :
        (∑ f : Fin r → Fin 2, ∑ g : Fin r → Fin 2,
          ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
            ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
        ∑ p : (Fin r → Fin 2) × (Fin r → Fin 2),
          ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (p.1 e) (p.2 e) : ℝ) : ℂ) *
            ((Bcomp (b e) (p.1 e) (p.2 e) : ℝ) : ℂ) :=
      (Fintype.sum_prod_type (fun p : (Fin r → Fin 2) × (Fin r → Fin 2) =>
        ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (p.1 e) (p.2 e) : ℝ) : ℂ) *
          ((Bcomp (b e) (p.1 e) (p.2 e) : ℝ) : ℂ))).symm
    rw [hprod_sum]
    have heqv := Fintype.sum_equiv (prodFunEquiv r)
      (fun p => ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (p.1 e) (p.2 e) : ℝ) : ℂ) *
        ((Bcomp (b e) (p.1 e) (p.2 e) : ℝ) : ℂ))
      (fun q => ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (q e).1 (q e).2 : ℝ) : ℂ) *
        ((Bcomp (b e) (q e).1 (q e).2 : ℝ) : ℂ))
      (fun _ => rfl)
    rw [heqv, ← Fintype.prod_sum (fun e (fg : Fin 2 × Fin 2) =>
      (2 : ℂ) * ((Bcomp (a e) fg.1 fg.2 : ℝ) : ℂ) * ((Bcomp (b e) fg.1 fg.2 : ℝ) : ℂ))]
    rw [← prod_delta_eq a b]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [Fintype.sum_prod_type]
    have hreal : (∑ x : Fin 2, ∑ y : Fin 2, Bcomp (a e) x y * Bcomp (b e) x y) =
        if a e = b e then (1 : ℝ) / 2 else 0 := Bcomp_sum_ortho (a e) (b e)
    simp only [Fin.sum_univ_two]
    push_cast
    have hreal2 : Bcomp (a e) 0 0 * Bcomp (b e) 0 0 + Bcomp (a e) 0 1 * Bcomp (b e) 0 1 +
        (Bcomp (a e) 1 0 * Bcomp (b e) 1 0 + Bcomp (a e) 1 1 * Bcomp (b e) 1 1) =
        if a e = b e then (1 : ℝ) / 2 else 0 := by
      simpa [Fin.sum_univ_two] using hreal
    split_ifs with heq
    · have hreal3 : (Bcomp (a e) 0 0 : ℂ) * (Bcomp (b e) 0 0 : ℂ) +
          (Bcomp (a e) 0 1 : ℂ) * (Bcomp (b e) 0 1 : ℂ) +
          ((Bcomp (a e) 1 0 : ℂ) * (Bcomp (b e) 1 0 : ℂ) +
           (Bcomp (a e) 1 1 : ℂ) * (Bcomp (b e) 1 1 : ℂ)) = 1 / 2 := by
        have h' : Bcomp (a e) 0 0 * Bcomp (b e) 0 0 + Bcomp (a e) 0 1 * Bcomp (b e) 0 1 +
            (Bcomp (a e) 1 0 * Bcomp (b e) 1 0 + Bcomp (a e) 1 1 * Bcomp (b e) 1 1) =
            (1 : ℝ) / 2 := hreal2.trans (if_pos heq)
        have hc := congrArg (fun x : ℝ => (x : ℂ)) h'
        simpa using hc
      linear_combination 2 * hreal3
    · have hreal3 : (Bcomp (a e) 0 0 : ℂ) * (Bcomp (b e) 0 0 : ℂ) +
          (Bcomp (a e) 0 1 : ℂ) * (Bcomp (b e) 0 1 : ℂ) +
          ((Bcomp (a e) 1 0 : ℂ) * (Bcomp (b e) 1 0 : ℂ) +
           (Bcomp (a e) 1 1 : ℂ) * (Bcomp (b e) 1 1 : ℂ)) = 0 := by
        have h' : Bcomp (a e) 0 0 * Bcomp (b e) 0 0 + Bcomp (a e) 0 1 * Bcomp (b e) 0 1 +
            (Bcomp (a e) 1 0 * Bcomp (b e) 1 0 + Bcomp (a e) 1 1 * Bcomp (b e) 1 1) =
            (0 : ℝ) := hreal2.trans (if_neg heq)
        have hc := congrArg (fun x : ℝ => (x : ℂ)) h'
        simpa using hc
      linear_combination 2 * hreal3
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, f]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  have hterm2 (a b : Fin r → Fin 4) :
      (∑ f : Fin r → Fin 2, ∑ g : Fin r → Fin 2,
        star (v a) * w b * ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
          ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
      if a = b then star (v a) * w b else 0 := by
    have hpull :
        (∑ f : Fin r → Fin 2, ∑ g : Fin r → Fin 2,
          star (v a) * w b * ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
            ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ)) =
        star (v a) * w b * ∑ f : Fin r → Fin 2, ∑ g : Fin r → Fin 2,
          ∏ e : Fin r, (2 : ℂ) * ((Bcomp (a e) (f e) (g e) : ℝ) : ℂ) *
            ((Bcomp (b e) (f e) (g e) : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => (Finset.mul_sum _ _ _).symm
    rw [hpull, h2 a b]
    split_ifs <;> ring
  simp_rw [hterm2]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl
