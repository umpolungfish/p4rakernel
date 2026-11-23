/-
  Imscribing/YangMills/IIDSchwinger.lean

  Explicit Schwinger function from a non-Gaussian independent field.  Its
  value depends only on the equality classes of the argument tuple, which
  makes SO(4) and translation invariance, reflection positivity, exponential
  clustering and non-Gaussianity direct computations.
-/
import Mathlib
import Imscribing.YangMills.Core

set_option maxHeartbeats 8000000

open scoped BigOperators
open Complex Real Filter Matrix

namespace YangMills

/-- Moments of the law Z = 1 or 2 with equal weight. -/
noncomputable def iidMom (k : ℕ) : ℂ := (((1 : ℂ) ^ k + (2 : ℂ) ^ k) / 2)

private lemma iidMom_one : iidMom 1 = ((3 / 2 : ℝ) : ℂ) := by norm_num [iidMom]
private lemma iidMom_two : iidMom 2 = 5 / 2 := by norm_num [iidMom]
private lemma iidMom_three : iidMom 3 = 9 / 2 := by norm_num [iidMom]
private lemma iidMom_four : iidMom 4 = 17 / 2 := by norm_num [iidMom]

/-- Equality classes of a finite family of points. -/
noncomputable def iidClasses {n : ℕ} (xs : Fin n → Space4) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin n => Finset.univ.filter (fun j : Fin n => xs j = xs i))

/-- The Schwinger function: product of moments over equality classes. -/
noncomputable def iidSchwinger (n : ℕ) (xs : Fin n → Space4) : ℂ :=
  (iidClasses xs).prod (fun C => iidMom C.card)

/-! ### Invariance under injective ambient maps -/

lemma iidClasses_map {n : ℕ} (xs : Fin n → Space4) (g : Space4 → Space4)
    (hg : Function.Injective g) :
    iidClasses (fun i => g (xs i)) = iidClasses xs := by
  unfold iidClasses
  congr 1
  funext i
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => hg h
  · exact fun h => congrArg g h

lemma iidSchwinger_map {n : ℕ} (xs : Fin n → Space4) (g : Space4 → Space4)
    (hg : Function.Injective g) :
    iidSchwinger n (fun i => g (xs i)) = iidSchwinger n xs := by
  unfold iidSchwinger
  rw [iidClasses_map xs g hg]

/-! ### Property 1: Euclidean translation invariance -/

lemma iidSchwinger_trans {n : ℕ} (a : Space4) (xs : Fin n → Space4) :
    iidSchwinger n (fun i j => xs i j + a j) = iidSchwinger n xs := by
  apply iidSchwinger_map xs (fun x => fun j => x j + a j)
  intro x y h
  funext j
  exact add_right_cancel (congrFun h j)

/-! ### Property 2: continuous SO(4) invariance -/

lemma so4_mulVec_injective (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ) :
    Function.Injective (fun x : Space4 => Matrix.mulVec R.1 x) := by
  intro x y h
  change Matrix.mulVec R.1 x = Matrix.mulVec R.1 y at h
  have hmul : (R⁻¹).1 * R.1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
    congrArg Subtype.val (inv_mul_cancel R)
  calc
    x = Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) x := by simp
    _ = Matrix.mulVec ((R⁻¹).1 * R.1) x := by rw [hmul]
    _ = Matrix.mulVec (R⁻¹).1 (Matrix.mulVec R.1 x) := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (R⁻¹).1 (Matrix.mulVec R.1 y) := by rw [h]
    _ = Matrix.mulVec ((R⁻¹).1 * R.1) y := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) y := by rw [hmul]
    _ = y := by simp

lemma iidSchwinger_so4 (n : ℕ) (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
    (xs : Fin n → Space4) :
    iidSchwinger n (fun i => Matrix.mulVec R.1 (xs i)) = iidSchwinger n xs := by
  exact iidSchwinger_map xs (fun x => Matrix.mulVec R.1 x) (so4_mulVec_injective R)

/-! ### Property 3: reflection positivity -/

lemma timeReflect_neg (x : Space4) (hpos : 0 < x 0) (y : Space4) (hypos : 0 < y 0) :
    euclidTimeReflect x ≠ y := by
  intro h
  have h0 := congrFun h 0
  dsimp [euclidTimeReflect] at h0
  linarith

private lemma iidSchwinger_pair_ne (x y : Space4) (h : x ≠ y) :
    iidSchwinger 2 ![x, y] = iidMom 1 * iidMom 1 := by
  unfold iidSchwinger iidClasses
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.image_insert, Finset.image_singleton]
  have h' : y ≠ x := fun hyx => h hyx.symm
  have h0 : ({0, 1} : Finset (Fin 2)).filter (fun j => ![x, y] j = ![x, y] (0 : Fin 2)) = {0} := by
    ext j; fin_cases j <;> simp [h, h']
  have h1 : ({0, 1} : Finset (Fin 2)).filter (fun j => ![x, y] j = ![x, y] (1 : Fin 2)) = {1} := by
    ext j; fin_cases j <;> simp [h, h']
  rw [h0, h1]
  simp [iidMom_one]

lemma iidSchwinger_refl_pos_2 (m : ℕ) (c : Fin m → ℂ) (xs : Fin m → Space4)
    (hpos : ∀ i, 0 < xs i 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        iidSchwinger 2 ![euclidTimeReflect (xs i), xs j]).re := by
  have hdisc : ∀ i j, euclidTimeReflect (xs i) ≠ xs j := fun i j => timeReflect_neg (xs i) (hpos i) (xs j) (hpos j)
  simp_rw [iidSchwinger_pair_ne _ _ (hdisc _ _)]
  have hrewrite : (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) * (iidMom 1 * iidMom 1)) =
      (∑ i : Fin m, c i * iidMom 1) * starRingEnd ℂ (∑ j : Fin m, c j * iidMom 1) := by
    have hm : starRingEnd ℂ (iidMom 1) = iidMom 1 := by
      rw [iidMom_one]
      exact conj_ofReal (3 / 2 : ℝ)
    calc
      (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * (iidMom 1 * iidMom 1))
          = ∑ i : Fin m, ∑ j : Fin m, (c i * iidMom 1) * (starRingEnd ℂ (c j) * iidMom 1) := by
              apply Finset.sum_congr rfl; intro i hi
              apply Finset.sum_congr rfl; intro j hj
              ring
      _ = ∑ i : Fin m, (c i * iidMom 1) * (∑ j : Fin m, starRingEnd ℂ (c j) * iidMom 1) := by
              apply Finset.sum_congr rfl; intro i hi
              rw [Finset.mul_sum]
      _ = (∑ i : Fin m, c i * iidMom 1) * (∑ j : Fin m, starRingEnd ℂ (c j) * iidMom 1) := by
              rw [Finset.sum_mul]
      _ = (∑ i : Fin m, c i * iidMom 1) * starRingEnd ℂ (∑ j : Fin m, c j * iidMom 1) := by
              rw [map_sum]
              apply congrArg (fun z : ℂ => (∑ i : Fin m, c i * iidMom 1) * z)
              apply Finset.sum_congr rfl; intro j hj
              rw [map_mul, hm]
  rw [hrewrite]
  have hre : ((∑ i : Fin m, c i * iidMom 1) * starRingEnd ℂ (∑ i : Fin m, c i * iidMom 1)).re =
      Complex.normSq (∑ i : Fin m, c i * iidMom 1) := by
    rw [Complex.mul_conj]
    simp
  rw [hre]
  exact Complex.normSq_nonneg _

/-! ### Property 4: exponential clustering -/

lemma iidMom_norm_le (k : ℕ) : ‖iidMom k‖ ≤ (2 : ℝ) ^ k := by
  unfold iidMom
  rw [norm_div]
  norm_num
  have hle0 : ‖((1 : ℂ) ^ k + (2 : ℂ) ^ k)‖ ≤ 1 + (2 : ℝ) ^ k := by
    calc
      ‖((1 : ℂ) ^ k + (2 : ℂ) ^ k)‖ ≤ ‖(1 : ℂ) ^ k‖ + ‖(2 : ℂ) ^ k‖ := norm_add_le _ _
      _ = 1 + (2 : ℝ) ^ k := by simp
  have hle : ‖((1 : ℂ) ^ k + (2 : ℂ) ^ k)‖ ≤ 1 + (2 : ℝ) ^ k := hle0
  have htwo : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  norm_num at hle ⊢
  nlinarith

private lemma iidSchwinger_norm_le {n : ℕ} (xs : Fin n → Space4) :
    ‖iidSchwinger n xs‖ ≤ (2 : ℝ) ^ (n * n) := by
  unfold iidSchwinger
  have hcard : ∀ C ∈ iidClasses xs, C.card ≤ n := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨i, hi, hEq⟩
    rw [← hEq]
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
      (p := fun j : Fin n => xs j = xs i))
  calc
    ‖(iidClasses xs).prod (fun C => iidMom C.card)‖
        ≤ (iidClasses xs).prod (fun C => ‖iidMom C.card‖) :=
          (Finset.norm_prod_le (α := ℂ) (s := iidClasses xs) (f := fun C => iidMom C.card))
    _ ≤ (iidClasses xs).prod (fun C => (2 : ℝ) ^ n) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro C hC
      exact le_trans (iidMom_norm_le C.card)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hcard C hC))
    _ = ((2 : ℝ) ^ n) ^ (iidClasses xs).card := by simp
    _ ≤ ((2 : ℝ) ^ n) ^ n := by
      have hnum : (iidClasses xs).card ≤ n := by
        unfold iidClasses
        simpa using (@Finset.card_image_le (Fin n) (Finset (Fin n))
          (Finset.univ : Finset (Fin n))
          (fun i => (Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs i))
          inferInstance)
      exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hnum
    _ = (2 : ℝ) ^ (n * n) := by ring_nf


/-! ### Factorization over separated families -/

private lemma class_castAdd_eq {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) (i : Fin n) :
    (Finset.univ.filter (fun k : Fin (n+m) =>
        Fin.append xs ys k = Fin.append xs ys (Fin.castAdd m i))) =
      ((Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs i)).image (Fin.castAdd m) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
  constructor
  · intro hk
    induction k using Fin.addCases with
    | left j =>
        refine ⟨j, ?_, rfl⟩
        simpa using hk
    | right j =>
        exfalso
        have hval : ys j = xs i := by simpa using hk
        exact hdisj _ _ hval.symm
  · rintro ⟨j, hj, rfl⟩
    simpa using hj

private lemma class_natAdd_eq {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) (j : Fin m) :
    (Finset.univ.filter (fun k : Fin (n+m) =>
        Fin.append xs ys k = Fin.append xs ys (Fin.natAdd n j))) =
      ((Finset.univ : Finset (Fin m)).filter (fun l => ys l = ys j)).image (Fin.natAdd n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
  constructor
  · intro hk
    induction k using Fin.addCases with
    | left l =>
        exfalso
        have hval : xs l = ys j := by simpa using hk
        exact hdisj _ _ hval
    | right l =>
        refine ⟨l, ?_, rfl⟩
        simpa using hk
  · rintro ⟨l, hl, rfl⟩
    simpa using hl

lemma iidClasses_append_disjoint {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) :
    iidClasses (Fin.append xs ys) =
      (iidClasses xs).image (fun C => C.image (Fin.castAdd m)) ∪
      (iidClasses ys).image (fun C => C.image (Fin.natAdd n)) := by
  unfold iidClasses
  ext C
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left i0 =>
        left
        refine ⟨(Finset.univ : Finset (Fin n)).filter (fun j => xs j = xs i0), ?_, ?_⟩
        · exact ⟨i0, rfl⟩
        · exact (class_castAdd_eq xs ys hdisj i0).symm
    | right j0 =>
        right
        refine ⟨(Finset.univ : Finset (Fin m)).filter (fun l => ys l = ys j0), ?_, ?_⟩
        · exact ⟨j0, rfl⟩
        · exact (class_natAdd_eq xs ys hdisj j0).symm
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · rcases hi with ⟨⟨a, ha⟩, hC⟩
      rw [← hC, ← ha]
      refine ⟨Fin.castAdd m a, ?_⟩
      exact class_castAdd_eq xs ys hdisj a
    · rcases hj with ⟨⟨a, ha⟩, hC⟩
      rw [← hC, ← ha]
      refine ⟨Fin.natAdd n a, ?_⟩
      exact class_natAdd_eq xs ys hdisj a

lemma iidClasses_append_img_disjoint {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) : Disjoint
      ((iidClasses xs).image (fun C => C.image (Fin.castAdd m)))
      ((iidClasses ys).image (fun C => C.image (Fin.natAdd n))) := by
  rw [Finset.disjoint_left]
  intro C1 hC1 hC2
  rcases Finset.mem_image.mp hC1 with ⟨A, hA, rfl⟩
  rcases Finset.mem_image.mp hC2 with ⟨B, hB, hEq⟩
  rcases Finset.mem_image.mp hA with ⟨i0, hi0, hiEq⟩
  have hiMem : i0 ∈ A := by rw [← hiEq]; simp
  have ht1 : Fin.castAdd m i0 ∈ A.image (Fin.castAdd m) := Finset.mem_image.mpr ⟨i0, hiMem, rfl⟩
  have ht2 : Fin.castAdd m i0 ∈ B.image (Fin.natAdd n) := by rw [hEq]; exact ht1
  rcases Finset.mem_image.mp ht2 with ⟨j, hj, heq⟩
  have hfin : (i0.castAdd m : Fin (n+m)) = Fin.natAdd n j := by simpa using heq.symm
  have happ := congrArg (Fin.append xs ys) hfin
  have hxy : xs i0 = ys j := by simpa using happ
  exact hdisj i0 j hxy

lemma iidSchwinger_append {n m : ℕ} (xs : Fin n → Space4) (ys : Fin m → Space4)
    (hdisj : ∀ i j, xs i ≠ ys j) :
    iidSchwinger (n+m) (Fin.append xs ys) = iidSchwinger n xs * iidSchwinger m ys := by
  unfold iidSchwinger
  rw [iidClasses_append_disjoint xs ys hdisj]
  have hdisjImg := iidClasses_append_img_disjoint xs ys hdisj
  rw [Finset.prod_union hdisjImg]
  congr 1
  · rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro C hC
      rw [Finset.card_image_of_injective _ (Fin.castAdd_injective n m)]
    · intro a ha b hb hab
      exact Finset.image_injective (Fin.castAdd_injective n m) hab
  · rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro C hC
      rw [Finset.card_image_of_injective _ (Fin.natAdd_injective m n)]
    · intro a ha b hb hab
      exact Finset.image_injective (Fin.natAdd_injective m n) hab

lemma iidSchwinger_cluster (n m : ℕ) :
    ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4) (R : ℝ),
      0 ≤ R → (∀ i j, R ≤ ‖xs i - ys j‖) →
      ‖iidSchwinger (n+m) (Fin.append xs ys) - iidSchwinger n xs * iidSchwinger m ys‖
        ≤ C * Real.exp (-(1 * R)) := by
  refine ⟨(2 : ℝ) ^ ((n+m)*(n+m)) + (2 : ℝ) ^ (n*n + m*m), ?_⟩
  intro xs ys R hR hsep
  by_cases hR0 : R = 0
  · subst R
    norm_num
    calc
      ‖iidSchwinger (n+m) (Fin.append xs ys) - iidSchwinger n xs * iidSchwinger m ys‖
          ≤ ‖iidSchwinger (n+m) (Fin.append xs ys)‖ + ‖iidSchwinger n xs * iidSchwinger m ys‖ := norm_sub_le _ _
      _ = ‖iidSchwinger (n+m) (Fin.append xs ys)‖ + ‖iidSchwinger n xs‖ * ‖iidSchwinger m ys‖ := by rw [norm_mul]
      _ ≤ (2 : ℝ) ^ ((n+m)*(n+m)) + (2 : ℝ) ^ (n*n) * (2 : ℝ) ^ (m*m) := by
        gcongr <;> apply iidSchwinger_norm_le
      _ = (2 : ℝ) ^ ((n+m)*(n+m)) + (2 : ℝ) ^ (n*n + m*m) := by rw [← pow_add]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    have hdisj : ∀ i j, xs i ≠ ys j := by
      intro i j hij
      have hz : ‖xs i - ys j‖ = 0 := by rw [hij, sub_self, norm_zero]
      have : R ≤ 0 := by simpa [hz] using hsep i j
      linarith
    rw [iidSchwinger_append xs ys hdisj, sub_self, norm_zero]
    positivity

/-! ### Property 5: non-Gaussian -/

lemma iidSchwinger_non_gaussian :
    ∃ xs : Fin 4 → Space4, connected4 iidSchwinger xs ≠ 0 := by
  let xs : Fin 4 → Space4 := fun _ => 0
  refine ⟨xs, ?_⟩
  dsimp [connected4]
  have h1 : ∀ k (hk : k ≠ 0) (zs : Fin k → Space4), (∀ i, zs i = 0) →
      iidSchwinger k zs = iidMom k := by
    intro k hk zs hz
    haveI : NeZero k := ⟨hk⟩
    unfold iidSchwinger iidClasses
    have hs : (Finset.univ.image (fun i : Fin k =>
        Finset.univ.filter (fun j : Fin k => zs j = zs i))) = {Finset.univ} := by
      ext C
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        ext j
        simp [hz]
      · intro h
        subst C
        refine ⟨0, ?_⟩
        ext j
        simp [hz]
    rw [hs]
    simp
  rw [h1 4 (by omega) _ (fun _ => rfl),
      h1 1 (by omega) _ (fun i => by fin_cases i; rfl),
      h1 2 (by omega) _ (fun i => by fin_cases i <;> rfl),
      h1 3 (by omega) _ (fun i => by fin_cases i <;> rfl)]
  rw [iidMom_one, iidMom_two, iidMom_three, iidMom_four]
  norm_num

end YangMills

#print axioms YangMills.iidSchwinger_trans
#print axioms YangMills.iidSchwinger_so4
#print axioms YangMills.iidSchwinger_refl_pos_2
#print axioms YangMills.iidSchwinger_cluster
#print axioms YangMills.iidSchwinger_non_gaussian

namespace YangMills

/-! ### Property 6: permutation symmetry (item 8 of the Clay decomposition) -/

lemma iidClasses_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4) :
    iidClasses (fun i => xs (σ i)) = (iidClasses xs).image (fun C => C.image σ.symm) := by
  unfold iidClasses
  ext C
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Finset.univ.filter (fun j => xs j = xs (σ i)), ⟨σ i, rfl⟩, ?_⟩
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hj
      exact ⟨σ j, hj, by simp⟩
  · rintro ⟨A, ⟨i, rfl⟩, rfl⟩
    refine ⟨σ.symm i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hj
      exact ⟨σ j, by simpa using hj, by simp⟩
    · rintro ⟨k, hk, hval⟩
      have : k = σ j := by simpa using congrArg σ hval
      subst k
      simpa using hk

lemma iidSchwinger_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4) :
    iidSchwinger n (fun i => xs (σ i)) = iidSchwinger n xs := by
  unfold iidSchwinger
  rw [iidClasses_perm]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro C hC
    rw [Finset.card_image_of_injective _ σ.symm.injective]
  · intro a ha b hb hab
    exact Finset.image_injective σ.symm.injective hab

#print axioms YangMills.iidSchwinger_perm

end YangMills
