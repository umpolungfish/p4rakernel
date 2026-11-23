import Mathlib
import Imscribing.YangMills.IIDSchwinger
import Imscribing.YangMills.IIDWilsonLimit
import Imscribing.YangMills.IIDOS

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators
open Complex Real Filter

namespace YangMills

noncomputable def constMomSchwinger (p : ℂ) (n : ℕ) (xs : Fin n → Space4) : ℂ :=
  p ^ (iidClasses xs).card

lemma constMom_map (p : ℂ) {n : ℕ} (xs : Fin n → Space4) (g : Space4 → Space4)
    (hg : Function.Injective g) :
    constMomSchwinger p n (fun i => g (xs i)) = constMomSchwinger p n xs := by
  unfold constMomSchwinger
  rw [iidClasses_map xs g hg]

lemma constMom_trans (p : ℂ) {n : ℕ} (a : Space4) (xs : Fin n → Space4) :
    constMomSchwinger p n (fun i j => xs i j + a j) = constMomSchwinger p n xs := by
  apply constMom_map p xs (fun x => fun j => x j + a j)
  intro x y h
  funext j
  exact add_right_cancel (congrFun h j)

lemma constMom_so4 (p : ℂ) (n : ℕ) (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
    (xs : Fin n → Space4) :
    constMomSchwinger p n (fun i => Matrix.mulVec R.1 (xs i)) = constMomSchwinger p n xs :=
  constMom_map p xs (fun x => Matrix.mulVec R.1 x) (so4_mulVec_injective R)

lemma constMom_perm (p : ℂ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4) :
    constMomSchwinger p n (fun i => xs (σ i)) = constMomSchwinger p n xs := by
  unfold constMomSchwinger
  rw [iidClasses_perm]
  exact congrArg (fun k => p ^ k)
    (Finset.card_image_of_injective (iidClasses xs)
      (fun a b hab => Finset.image_injective σ.symm.injective hab))

lemma constMom_append (p : ℂ) {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) :
    constMomSchwinger p (n + m) (Fin.append xs ys) =
      constMomSchwinger p n xs * constMomSchwinger p m ys := by
  unfold constMomSchwinger
  rw [iidClasses_append_disjoint xs ys hdisj]
  rw [Finset.card_union_of_disjoint (iidClasses_append_img_disjoint xs ys hdisj)]
  rw [Finset.card_image_of_injective (iidClasses xs)
        (fun a b hab => Finset.image_injective (Fin.castAdd_injective n m) hab)]
  rw [Finset.card_image_of_injective (iidClasses ys)
        (fun a b hab => Finset.image_injective (Fin.natAdd_injective m n) hab)]
  exact pow_add p (iidClasses xs).card (iidClasses ys).card

lemma constMom_refl_pos_n (p : ℝ) (m : ℕ) (n_pts : Fin m → ℕ)
    (c : Fin m → ℂ) (xs : ∀ i : Fin m, Fin (n_pts i) → Space4)
    (hpos : ∀ i k, 0 < (xs i k) 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        constMomSchwinger (p : ℂ) (n_pts i + n_pts j)
          (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re := by
  have hdisc : ∀ i j k l, euclidTimeReflect (xs i k) ≠ xs j l := fun i j k l =>
    timeReflect_neg (xs i k) (hpos i k) (xs j l) (hpos j l)
  have hfactor : ∀ i j,
      constMomSchwinger (p : ℂ) (n_pts i + n_pts j)
        (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j)) =
      constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k)) *
        constMomSchwinger (p : ℂ) (n_pts j) (xs j) := fun i j =>
    constMom_append (p : ℂ) (fun k => euclidTimeReflect (xs i k)) (xs j) (hdisc i j)
  simp_rw [hfactor]
  let A : Fin m → ℂ := fun i =>
    c i * constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k))
  have hpconj : starRingEnd ℂ (p : ℂ) = (p : ℂ) := Complex.conj_ofReal p
  have hcaptured : ∀ i,
      starRingEnd ℂ (constMomSchwinger (p : ℂ) (n_pts i)
        (fun k => euclidTimeReflect (xs i k))) =
      constMomSchwinger (p : ℂ) (n_pts i) (xs i) := by
    intro i
    unfold constMomSchwinger
    rw [map_pow, hpconj, iidClasses_map (xs i) euclidTimeReflect euclidTimeReflect_injective]
  have hrewrite :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          (constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k)) *
           constMomSchwinger (p : ℂ) (n_pts j) (xs j))) =
      (∑ i : Fin m, A i) * starRingEnd ℂ (∑ i : Fin m, A i) := by
    unfold A
    calc
      (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            (constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k)) *
             constMomSchwinger (p : ℂ) (n_pts j) (xs j)))
          = ∑ i : Fin m, ∑ j : Fin m,
              (c i * constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
                (starRingEnd ℂ (c j) * constMomSchwinger (p : ℂ) (n_pts j) (xs j)) := by
              apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ i : Fin m,
              (c i * constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
              (∑ j : Fin m, starRingEnd ℂ (c j) * constMomSchwinger (p : ℂ) (n_pts j) (xs j)) := by
              apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ = (∑ i : Fin m,
              c i * constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
              (∑ j : Fin m, starRingEnd ℂ (c j) * constMomSchwinger (p : ℂ) (n_pts j) (xs j)) := by
              rw [Finset.sum_mul]
      _ = (∑ i : Fin m,
              c i * constMomSchwinger (p : ℂ) (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
              starRingEnd ℂ (∑ j : Fin m,
                c j * constMomSchwinger (p : ℂ) (n_pts j)
                  (fun k => euclidTimeReflect (xs j k))) := by
              congr 1
              rw [map_sum]
              apply Finset.sum_congr rfl; intro j _
              rw [map_mul, hcaptured j]
  rw [hrewrite, Complex.mul_conj]
  exact Complex.normSq_nonneg _

lemma constMom_cluster (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n m : ℕ) :
    ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4) (R : ℝ),
      0 ≤ R → (∀ i j, R ≤ ‖xs i - ys j‖) →
      ‖constMomSchwinger (p : ℂ) (n+m) (Fin.append xs ys) -
        constMomSchwinger (p : ℂ) n xs * constMomSchwinger (p : ℂ) m ys‖
        ≤ C * Real.exp (-(1 * R)) := by
  refine ⟨2, ?_⟩
  intro xs ys R hR hsep
  by_cases hR0 : R = 0
  · subst R
    simp
    have hb1 : ‖constMomSchwinger (p : ℂ) (n+m) (Fin.append xs ys)‖ ≤ 1 := by
      unfold constMomSchwinger
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
      exact pow_le_one₀ hp hp1
    have hbx : ‖constMomSchwinger (p : ℂ) n xs‖ ≤ 1 := by
      unfold constMomSchwinger
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
      exact pow_le_one₀ hp hp1
    have hby : ‖constMomSchwinger (p : ℂ) m ys‖ ≤ 1 := by
      unfold constMomSchwinger
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
      exact pow_le_one₀ hp hp1
    have hb2 : ‖constMomSchwinger (p : ℂ) n xs * constMomSchwinger (p : ℂ) m ys‖ ≤ 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg (constMomSchwinger (p : ℂ) n xs),
                 norm_nonneg (constMomSchwinger (p : ℂ) m ys)]
    calc
      ‖constMomSchwinger (p : ℂ) (n+m) (Fin.append xs ys) -
          constMomSchwinger (p : ℂ) n xs * constMomSchwinger (p : ℂ) m ys‖
          ≤ ‖constMomSchwinger (p : ℂ) (n+m) (Fin.append xs ys)‖ +
            ‖constMomSchwinger (p : ℂ) n xs * constMomSchwinger (p : ℂ) m ys‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hb1 hb2
      _ ≤ 2 := by norm_num
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    have hdisj : ∀ i j, xs i ≠ ys j := by
      intro i j hij
      have := hsep i j
      rw [hij, sub_self, norm_zero] at this
      linarith
    unfold constMomSchwinger
    rw [iidClasses_append_disjoint xs ys hdisj]
    rw [Finset.card_union_of_disjoint (iidClasses_append_img_disjoint xs ys hdisj)]
    have hinj1 : Function.Injective
        (fun C : Finset (Fin n) => C.image (Fin.castAdd m)) :=
      Finset.image_injective (Fin.castAdd_injective n m)
    have hinj2 : Function.Injective
        (fun C : Finset (Fin m) => C.image (Fin.natAdd n)) :=
      Finset.image_injective (Fin.natAdd_injective m n)
    rw [Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2]
    rw [← pow_add]
    ring_nf
    simp [abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    positivity



lemma cls_all_eq {n : ℕ} [NeZero n] (xs : Fin n → Space4) (x : Space4)
    (h : ∀ i, xs i = x) : (iidClasses xs).card = 1 := by
  unfold iidClasses
  have hf : (fun i : Fin n => (Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs i)) =
      (fun _ : Fin n => (Finset.univ : Finset (Fin n))) := by
    funext i; ext j; simp [h j, h i]
  rw [hf, Finset.image_const Finset.univ_nonempty]
  simp

lemma cls_two_classes {n : ℕ} (xs : Fin n → Space4) (a b : Fin n) (hab : xs a ≠ xs b)
    (hall : ∀ i, xs i = xs a ∨ xs i = xs b) : (iidClasses xs).card = 2 := by
  let Fa := (Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs a)
  let Fb := (Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs b)
  have hFaFb : Fa ≠ Fb := by
    intro heq
    have haFa : a ∈ Fa := by simp [Fa]
    have haFb : a ∈ Fb := by simpa [heq] using haFa
    have hx : xs a = xs b := by simpa [Fb] using haFb
    exact hab hx
  rw [Finset.card_eq_two]
  refine ⟨Fa, Fb, hFaFb, ?_⟩
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image.mp hC with ⟨i, hi, rfl⟩
    rcases hall i with hiA | hiB
    · rw [Finset.mem_insert, Finset.mem_singleton]; left
      ext j; simp [Fa, hiA]
    · rw [Finset.mem_insert, Finset.mem_singleton]; right
      ext j; simp [Fb, hiB]
  · intro hC
    rw [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with hC | hC
    · subst hC
      exact Finset.mem_image.mpr ⟨a, by simp, by ext j; simp [Fa]⟩
    · subst hC
      exact Finset.mem_image.mpr ⟨b, by simp, by ext j; simp [Fb]⟩

lemma constMom_const (p : ℂ) {n : ℕ} [NeZero n] (x : Space4) :
    constMomSchwinger p n (fun _ : Fin n => x) = p := by
  unfold constMomSchwinger
  rw [cls_all_eq (fun _ : Fin n => x) x (fun i => rfl)]
  simp

@[simp] lemma cm1 (p : ℂ) : constMomSchwinger p 1 (![0] : Fin 1 → Space4) = p := by
  rw [show (![0] : Fin 1 → Space4) = fun _ => 0 by funext i; fin_cases i; rfl]
  exact constMom_const p 0
@[simp] lemma cm2 (p : ℂ) : constMomSchwinger p 2 (![0,0] : Fin 2 → Space4) = p := by
  rw [show (![0,0] : Fin 2 → Space4) = fun _ => 0 by funext i; fin_cases i <;> rfl]
  exact constMom_const p 0
@[simp] lemma cm3 (p : ℂ) : constMomSchwinger p 3 (![0,0,0] : Fin 3 → Space4) = p := by
  rw [show (![0,0,0] : Fin 3 → Space4) = fun _ => 0 by funext i; fin_cases i <;> rfl]
  exact constMom_const p 0

end YangMills
