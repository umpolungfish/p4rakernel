import Imscribing.Millennium.Erdos.CollatzAmplitudeCocycle

/-! Complete residue-refinement mass of the retained predecessor recursion.
The sum fold keeps every class and both predecessor arms. It is distinct
from the fixed-root amplitude limit and from the cycle-cut native census. -/
namespace CollatzDepthSplit
open scoped BigOperators Topology
open Filter

private theorem sum_mod_permutation (d : ℕ) (F f : ℕ → ℕ)
    (hinj : Set.InjOn (fun i => f i % 3 ^ d) (Finset.range (3 ^ d)))
    (hF : ∀ v, F v = F (v % 3 ^ d)) :
    (∑ i ∈ Finset.range (3 ^ d), F (f i)) = ∑ i ∈ Finset.range (3 ^ d), F i := by
  classical
  have hsub : (Finset.range (3 ^ d)).image (fun i => f i % 3 ^ d) ⊆
      Finset.range (3 ^ d) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  have heq : (Finset.range (3 ^ d)).image (fun i => f i % 3 ^ d) =
      Finset.range (3 ^ d) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj]
  calc
    (∑ i ∈ Finset.range (3 ^ d), F (f i)) =
        ∑ i ∈ Finset.range (3 ^ d), F (f i % 3 ^ d) :=
      Finset.sum_congr rfl (fun i _ => hF (f i))
    _ = ∑ i ∈ (Finset.range (3 ^ d)).image (fun i => f i % 3 ^ d), F i := by
      rw [Finset.sum_image hinj]
    _ = _ := by rw [heq]

private theorem sum_three_periods (N : ℕ) (F : ℕ → ℕ)
    (hp : ∀ v c, F (v + N * c) = F v) :
    (∑ i ∈ Finset.range (3 * N), F i) = 3 * ∑ i ∈ Finset.range N, F i := by
  have h₁ : (∑ i ∈ Finset.range N, F (N + i)) = ∑ i ∈ Finset.range N, F i := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa [Nat.mul_one, Nat.add_comm] using hp i 1
  have h₂ : (∑ i ∈ Finset.range N, F (N + N + i)) = ∑ i ∈ Finset.range N, F i := by
    apply Finset.sum_congr rfl
    intro i hi
    convert hp i 2 using 1 <;> congr 1 <;> omega
  rw [show 3 * N = (N + N) + N by omega,
    Finset.sum_range_add, Finset.sum_range_add, h₁, h₂]
  omega

/-- Complete count over the residue domain sufficient for depth `d`. -/
def residueSubtreeMass (d : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (3 ^ d), subtreeCount v d

lemma sum_subtree_double (d : ℕ) :
    (∑ v ∈ Finset.range (3 ^ d), subtreeCount (2 * v) d) = residueSubtreeMass d := by
  apply sum_mod_permutation d (fun v => subtreeCount v d) (fun v => 2 * v)
  · intro i hi j hj hij
    have h := double_inj_mod hij
    change i % 3 ^ d = j % 3 ^ d at h
    simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] using h
  · exact subtreeCount_mod_three_pow d

lemma sum_subtree_odd (d : ℕ) :
    (∑ v ∈ Finset.range (3 ^ d), subtreeCount (2 * v + 1) d) = residueSubtreeMass d := by
  apply sum_mod_permutation d (fun v => subtreeCount v d) (fun v => 2 * v + 1)
  · intro i hi j hj hij
    have h := arm_inj_mod hij
    simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] using h
  · exact subtreeCount_mod_three_pow d

lemma sum_subtree_junctions (d : ℕ) :
    (∑ v ∈ Finset.range (3 * 3 ^ d),
      if v % 3 = 2 then subtreeCount (2 * (v / 3) + 1) d else 0) =
        residueSubtreeMass d := by
  classical
  rw [← Finset.sum_filter]
  calc
    (∑ v ∈ (Finset.range (3 * 3 ^ d)).filter (fun v => v % 3 = 2),
      subtreeCount (2 * (v / 3) + 1) d) =
        ∑ v ∈ Finset.range (3 ^ d), subtreeCount (2 * v + 1) d := by
      apply Finset.sum_bij (fun v _ => v / 3)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
        omega
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        omega
      · intro b hb
        refine ⟨3 * b + 2, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
          omega
        · omega
      · intro v hv
        rfl
    _ = residueSubtreeMass d := sum_subtree_odd d

/-- Every coarse class contributes three doubling lifts and one odd lift;
the root contribution is retained separately. -/
theorem residueSubtreeMass_succ (d : ℕ) :
    residueSubtreeMass (d + 1) = 3 ^ (d + 1) + 4 * residueSubtreeMass d := by
  have heven : (∑ v ∈ Finset.range (3 * 3 ^ d), subtreeCount (2 * v) d) =
      3 * residueSubtreeMass d := by
    rw [sum_three_periods (3 ^ d) (fun v => subtreeCount (2 * v) d)]
    · rw [sum_subtree_double]
    · intro v c
      convert subtreeCount_period d (2 * v) (2 * c) using 1 <;> congr 1 <;> ring
  unfold residueSubtreeMass at ⊢
  simp only [subtreeCount_succ, Finset.sum_add_distrib]
  rw [show 3 ^ (d + 1) = 3 * 3 ^ d by ring]
  rw [heven, sum_subtree_junctions]
  simp [residueSubtreeMass] <;> ring

/-- Exact mass balance, with no equidistribution or limit assumption. -/
theorem residueSubtreeMass_exact (d : ℕ) :
    residueSubtreeMass d + 3 ^ (d + 1) = 4 ^ (d + 1) := by
  induction d with
  | zero => norm_num [residueSubtreeMass, subtreeCount]
  | succ d ih =>
    rw [residueSubtreeMass_succ]
    calc
      3 ^ (d + 1) + 4 * residueSubtreeMass d + 3 ^ (d + 1 + 1) =
          4 * (residueSubtreeMass d + 3 ^ (d + 1)) := by ring
      _ = 4 ^ (d + 1 + 1) := by rw [ih]; ring

/-- The complete-residue average, normalized by the observed growth scale.
Dividing the residue mean by `(4/3)^d` is exactly dividing its total by `4^d`. -/
noncomputable def meanNormalizedAmplitude (d : ℕ) : ℝ :=
  (residueSubtreeMass d : ℝ) / 4 ^ d

theorem meanNormalizedAmplitude_as_average (d : ℕ) :
    meanNormalizedAmplitude d =
      ((residueSubtreeMass d : ℝ) / (3 : ℝ) ^ d) / ((4 / 3 : ℝ) ^ d) := by
  unfold meanNormalizedAmplitude
  rw [div_pow]
  field_simp

theorem meanNormalizedAmplitude_exact (d : ℕ) :
    meanNormalizedAmplitude d = 4 - 3 * (3 / 4 : ℝ) ^ d := by
  have h : (residueSubtreeMass d : ℝ) + 3 ^ (d + 1) = 4 ^ (d + 1) := by
    exact_mod_cast residueSubtreeMass_exact d
  unfold meanNormalizedAmplitude
  rw [div_pow]
  apply (div_eq_iff (by positivity : (4 : ℝ) ^ d ≠ 0)).mpr
  rw [pow_succ, pow_succ] at h
  field_simp
  nlinarith

/-- The full refinement family has limiting mean amplitude four. This
keeps all residues and does not assert a limit at an individual integer. -/
theorem meanNormalizedAmplitude_limit :
    Tendsto meanNormalizedAmplitude atTop (𝓝 (4 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  have hl := (tendsto_const_nhds (x := (4 : ℝ))).sub (h.const_mul 3)
  apply (show Tendsto (fun d : ℕ => 4 - 3 * (3 / 4 : ℝ) ^ d) atTop
    (𝓝 (4 : ℝ)) by simpa using hl).congr
  intro d
  exact (meanNormalizedAmplitude_exact d).symm

end CollatzDepthSplit
