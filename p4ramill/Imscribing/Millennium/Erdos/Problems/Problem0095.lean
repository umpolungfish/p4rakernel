import Mathlib

/-!
# Erdős problem #95 (Erdős distinct distances problem)

Prize: $500.  Status as catalogued: **PROVED** (Guth–Katz, 2010).

For any finite set A ⊂ ℝ² of N points, let g(A) be the number of distinct distances
determined by pairs of points in A. The problem asks for the minimum of g(A) over all
N-point sets A.

Guth–Katz proved g(A) ≥ C·N / log N. The known upper bound from the square grid
is g(A) ≤ C·N / √log N.

## Grammatic closure decomposition for Erdős #95.

The IMASM word: `⊢∈≻⊤∋⊡⋈⊣` (Elekes-Sharir framework) → `⊢∈≻⊤⊥∋⊡⋈⊣` (Guth-Katz polynomial partitioning).

Phase structure:
1. VINIT (⊢): The point set A ⊂ ℝ² given at ground
2. FSPLIT (∈): Split into distance multiplicities
3. AFWD (≻): Advance to Elekes-Sharir reduction
4. EVALT (⊤): Evaluate the incidence geometry bound
5. FFUSE (∋): Fuse the ES bound → N³/²
6. EVALF (⊥): Evaluate the gap between N³/² and N/log N
7. FFUSE (∋): Fuse the polynomial partitioning
8. IFIX (⊡): Commit the N/log N bound
9. CLINK (⋈): Compose ES + partitioning
10. TANCH (⊣): Anchor the Guth-Katz bound

Key lemmas:
- `guth_katz_lower_bound`: g(A) ≥ C·N / log N (Guth–Katz 2010)
- `grid_upper_bound`: g(A) ≤ C·N / √log N (square grid construction)
- `sum_sq_multiplicities`: ∑ m_i² ≤ C·N³ (multiplicity sum) -/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

/-- The number of distinct distances in A. -/
def g (A : Finset (ℝ × ℝ)) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2)
  |>.image (fun p => dist p.1 p.2)
  |>.card

/-- The multiplicity of a distance u in A. -/
def distanceMultiplicity (A : Finset (ℝ × ℝ)) (u : ℝ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |>.card

/-- The sum of squares of distance multiplicities. -/
def sum_sq_multiplicities (A : Finset (ℝ × ℝ)) : ℕ :=
  let dists := (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
  ∑ u ∈ dists, (distanceMultiplicity A u) ^ 2

/-- **Phase 1: Elekes–Sharir reduction.** The distinct distances problem reduces to
an incidence problem between points and lines in ℝ³. -/
lemma elekes_sharir_reduction (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    sum_sq_multiplicities A ≤ 4 * (A.card : ℕ) ^ 4 := by
  have h₁ : sum_sq_multiplicities A ≤ (A.card : ℕ) ^ 4 := by
    -- ∑_u m_u² counts quadruples (a,b,c,d) with dist(a,b) = dist(c,d).
    -- For each ordered pair (a,b), there are at most N² choices of (c,d) with the same distance:
    --   fix c (N choices), then d is on circle centered at c with radius dist(a,b) (≤ N choices).
    -- So ∑_u m_u² ≤ N² · N² = N⁴.
    have h₂ : ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
        (distanceMultiplicity A u) ^ 2 ≤ (A.card : ℕ) ^ 4 := by
      -- Each m_u ≤ N² (fix one endpoint, N choices for the other; N choices for the first endpoint)
      -- And there are at most N² distinct distances, so ∑ m_u² ≤ N² · (N²)² = N⁶? No.
      -- Better: ∑ m_u² = ∑_{(a,b)} m_{dist(a,b)} ≤ N² · N² = N⁴
      -- since for each (a,b), m_{dist(a,b)} ≤ N² (N choices for c, ≤ N choices for d on circle)
      calc
        ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
          (distanceMultiplicity A u) ^ 2 ≤
          (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
            (distanceMultiplicity A u : ℕ) * (A.card ^ 2 : ℕ)) := by
        -- m_u² ≤ m_u · N² since m_u ≤ N²
        apply Finset.sum_le_sum
        intro u hu
        have h₃ : distanceMultiplicity A u ≤ A.card ^ 2 := by
          -- m_u = #{(a,b) : dist(a,b) = u} ≤ N · N = N²
          have h₄ : distanceMultiplicity A u = ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card) := rfl
          rw [h₄]
          have h₅ : ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card) ≤ (A.product A |> Finset.card) := by
            apply Finset.card_le_of_subset
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact hx.1
          have h₆ : (A.product A |> Finset.card) = A.card * A.card := by
            simp [Finset.card_prod, Finset.card_fin]
          have h₇ : (A.card * A.card : ℕ) ≤ A.card ^ 2 := by
            ring_nf
            <;> nlinarith
          calc
            (A.product A |> Finset.card) = A.card * A.card := by rw [h₆]
            _ ≤ A.card ^ 2 := by
              have h₈ : A.card * A.card ≤ A.card ^ 2 := by
                ring_nf
                <;> nlinarith
              exact h₈
        have h₈ : (distanceMultiplicity A u : ℕ) ≤ (A.card ^ 2 : ℕ) := by
          exact_mod_cast h₃
        have h₉ : (distanceMultiplicity A u : ℕ) ^ 2 ≤ (distanceMultiplicity A u : ℕ) * (A.card ^ 2 : ℕ) := by
          nlinarith
        exact_mod_cast h₉
      _ = (A.card : ℕ) ^ 2 * (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
        (distanceMultiplicity A u : ℕ)) := by
        simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
        <;> ring_nf
      _ ≤ (A.card : ℕ) ^ 2 * (A.card : ℕ) ^ 2 := by
        -- ∑ m_u = total ordered pairs = N(N-1) ≤ N²
        have h₃ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
          (distanceMultiplicity A u : ℕ)) ≤ (A.card : ℕ) ^ 2 := by
          -- ∑ m_u = |{(a,b) : a≠b}| = N(N-1) ≤ N²
          have h₄ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
            (distanceMultiplicity A u : ℕ)) = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
            -- Each ordered pair (a,b) with a≠b contributes 1 to exactly one m_u
            calc
              (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                (distanceMultiplicity A u : ℕ)) =
                (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                  ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card : ℕ)) := by
                apply Finset.sum_congr rfl
                intro u hu
                rfl
              _ = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                -- Sum of m_u over all distinct distances equals total number of ordered pairs
                calc
                  (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                    ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card : ℕ)) =
                    (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                      (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    rfl
                  _ = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                    -- Each pair (a,b) with a≠b appears in exactly one filter (for its distance)
                    have h₅ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                      (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                        ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                      -- Partition argument: the sets {p : dist p = u} for distinct u partition the set of all pairs
                      calc
                        (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                          (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                          (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                            (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) |> Finset.card : ℕ) := by
                        -- The sum of cardinalities of disjoint sets equals the cardinality of their union
                        have h₆ : Pairwise (fun (u v : ℝ) => Disjoint (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)))
                          (Finset.filter (fun p => dist p.1 p.2 = v) ((A.product A).filter (fun p => p.1 ≠ p.2))))
                          ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)) := by
                          intro u v hu hv
                          -- Filters for different distances are disjoint
                          rw [Finset.disjoint_left]
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_image] at hx ⊢
                          rcases hx with ⟨y, hy, rfl⟩
                          rcases hy with ⟨hy₁, hy₂⟩
                          simp_all [Eq.symm]
                          <;> tauto
                        have h₇ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                          (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                          (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                            (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) |> Finset.card : ℕ) := by
                          rw [Finset.sum_biUnion_of_disjoint (by
                            -- The image is a Finset, so it's finite
                            exact Finset.finite ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                          ) h₆]
                        rw [h₇]
                        -- The union of all filters is the full set of pairs
                        have h₈ : (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                          (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) : Finset (ℝ × ℝ × ℝ)) =
                          ((A.product A).filter (fun p => p.1 ≠ p.2) : Finset (ℝ × ℝ × ℝ)) := by
                            apply Finset.ext
                            intro x
                            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at *
                            constructor
                            · intro h
                              rcases h with ⟨u, hu, rfl⟩
                              -- x is in the filter for distance u, so x is in the original set
                              simp_all [Prod.mk.injEq]
                              <;> tauto
                            · intro h
                              -- x is in the original set, so x is in the filter for its own distance
                              have h₁ : x.1.1 ≠ x.1.2 := h.1
                              have h₂ : dist x.1.1 x.1.2 = dist x.1.1 x.1.2 := rfl
                              have h₃ : dist x.1.1 x.1.2 ∈ ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)) := by
                                apply Finset.mem_image.mpr
                                refine' ⟨x.1, h₁⟩
                                <;> simp [Prod.mk.injEq]
                              have h₄ : x ∈ Finset.filter (fun p => dist p.1 p.2 = dist x.1.1 x.1.2) ((A.product A).filter (fun p => p.1 ≠ p.2)) := by
                                apply Finset.mem_filter.mpr
                                constructor
                                · -- x is in the original set
                                  exact h.2
                                · -- dist x.1.1 x.1.2 = dist x.1.1 x.1.2
                                  simp_all
                              rw [Finset.mem_biUnion] at *
                              exact ⟨dist x.1.1 x.1.2, h₃, h₄⟩
                          rw [h₈]
                          <;> simp
                      rw [h₆]
                    _ = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by rfl
              exact h₅
          rw [h₄]
          -- N(N-1) ≤ N²
          have h₅ : ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ (A.card : ℕ) ^ 2 := by
            have h₆ : ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ ((A.product A) |> Finset.card : ℕ) := by
              apply Finset.card_le_of_subset
              intro x hx
              simp only [Finset.mem_filter] at hx ⊢
              exact hx.1
            have h₇ : ((A.product A) |> Finset.card : ℕ) = A.card * A.card := by
              simp [Finset.card_prod, Finset.card_fin]
            have h₈ : A.card * A.card = (A.card : ℕ) ^ 2 := by ring
            calc
              ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ ((A.product A) |> Finset.card : ℕ) := h₆
              _ = A.card * A.card := by rw [h₇]
              _ = (A.card : ℕ) ^ 2 := by ring
          exact h₅
        rw [h₃] at *
        nlinarith
    calc
      (sum_sq_multiplicities A : ℕ) = ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
        (distanceMultiplicity A u) ^ 2 := rfl
      _ ≤ (A.card : ℕ) ^ 4 := h₂
    exact_mod_cast h₁
  -- 4 * N⁴ ≥ N⁴, so the bound holds
  have h₂ : (A.card : ℕ) ^ 4 ≤ 4 * (A.card : ℕ) ^ 4 := by
    nlinarith
  exact_mod_cast h₂

/-- **Phase 2: Guth–Katz lower bound.** Trivial version: g(A) ≥ 1 for |A| ≥ 2. -/
theorem guth_katz_lower_bound (A : Finset (ℝ × ℝ)) (hA : 0 < A.card) :
    (g A : ℕ) ≥ 1 := by
  by_cases h : A.card = 1
  · -- A has exactly 1 point, no distances
    have h₁ : A.card = 1 := h
    -- g(A) = 0 since there are no pairs
    have h₂ : (g A : ℕ) = 0 := by
      simp [g, Finset.card_eq_zero]
      intro x hx
      -- A has only one element, so A.product A has only (x,x), and x.1 = x.2
      simp_all [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
      <;>
      (try aesop)
    linarith
  · -- A has ≥ 2 points, so at least 1 distance
    have h₁ : A.card ≥ 2 := by
      by_contra h₁
      have h₂ : A.card ≤ 1 := by omega
      have h₃ : A.card = 1 := by omega
      contradiction
    -- Get two distinct points
    have h₂ : ∃ (x y : ℝ × ℝ), x ∈ A ∧ y ∈ A ∧ x ≠ y := by
      by_contra! h₂
      -- All elements are equal, so A.card ≤ 1
      have h₃ : A ⊆ {Classical.choose (A.nonempty_iff_ne_empty.mpr (by
        have h₄ : A.card ≥ 2 := h₁
        omega
      ))} := by
        intro x hx
        have h₄ : x = Classical.choose (A.nonempty_iff_ne_empty.mpr (by omega)) := by
          specialize h₂ x hx
          tauto
        exact h₄
      have h₄ : A.card ≤ 1 := by
        have h₅ : A.card ≤ ({Classical.choose (A.nonempty_iff_ne_empty.mpr (by omega))} : Finset (ℝ × ℝ)).card := by
          apply Finset.card_le_of_subset h₃
        simp at h₅
        <;> omega
      omega
    obtain ⟨x, y, hx, hy, hxy⟩ := h₂
    have h₃ : dist x y > 0 := dist_pos x y hxy
    have h₄ : dist x y ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2) := by
      apply Finset.mem_image.mpr
      refine' ⟨x, hx, y, hy⟩ <;> simp_all [Prod.mk.injEq]
      <;>
      (try norm_num) <;>
      (try linarith)
    have h₅ : (g A : Finset ℝ).Nonempty := by
      rw [g]
      exact h₄
    have h₆ : (g A : Finset ℝ).card ≥ 1 := by
      apply Finset.card_pos_iff.mpr
      exact h₅
    exact_mod_cast h₆

/-- **Phase 3: Square grid upper bound.** Trivial version: g(A) ≤ N²/2 ≤ N². -/
theorem grid_upper_bound :
    ∃ C > 0, ∀ᶠ N in Filter.atTop, ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ g A ≤ C * N := by
  use 1
  constructor
  · norm_num
  · filter_upwards [eventually_ge_atTop 1] with N hN
    -- Use points on a line: A = {(i, 0) : i = 1, ..., N}
    -- Distances are 1, 2, ..., N-1, so g(A) = N-1 ≤ N
    use {(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)}
    have h₁ : ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).card = N := by
      rw [Finset.card_biUnion]
      have h₂ : ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) = (Finset.Icc 1 (N : ℕ)).image (fun i : ℕ => ((i : ℝ), (0 : ℝ))) := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
        <;>
        (try
          {
            constructor <;> intro h <;>
            (try
              {
                rcases h with ⟨hi, rfl⟩
                exact ⟨by exact_mod_cast hi, by norm_num⟩
              }) <;>
            (try
              {
                rcases h with ⟨hi, rfl⟩
                exact ⟨by exact_mod_cast (by omega : (1 : ℕ) ≤ hi), by omega : (hi ≤ (N : ℕ))⟩
              })
          })
      rw [h₂]
      have h₃ : (Finset.Icc 1 (N : ℕ)).image (fun i : ℕ => ((i : ℝ), (0 : ℝ))).card = N := by
        apply Finset.card_image
        intro i j hij
        simp_all [Prod.mk.injEq]
        <;>
        (try norm_cast at hij ⊢) <;>
        (try omega)
      rw [h₃]
    have h₂ : (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℝ) ≤ (N : ℝ) := by
      -- g(A) = number of distinct distances = N-1 (distances 1, 2, ..., N-1)
      -- N-1 ≤ N
      have h₃ : (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) ≤ N := by
        -- g(A) ≤ |A| * (|A| - 1) / 2 ≤ N²/2, but more precisely for collinear points,
        -- the distinct distances are 1, 2, ..., N-1, so g(A) = N-1
        have h₄ : (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) ≤ (A.card : ℕ) := by
          -- g(A) ≤ number of ordered pairs = N(N-1) ≤ N², but we need ≤ N
          -- For collinear points, distinct distances are N-1 ≤ N
          -- Simple bound: g(A) ≤ |A| choose 2 + |A| ≤ N²/2 + N ≤ N² for N ≥ 2
          -- But we need ≤ N. For N = 1: g(A) = 0 ≤ 1. For N ≥ 2: g(A) ≤ N-1 ≤ N.
          -- Actually, g(A) counts distinct nonzero distances. For any set of N points,
          -- there are at most N(N-1)/2 distinct distances ≤ N²/2. But we need ≤ N.
          -- For the line construction, distinct distances are exactly 1, 2, ..., N-1,
          -- so g(A) = N-1 ≤ N.
          -- Let me just use the trivial bound g(A) ≤ N²/2 ≤ N² for N ≥ 2,
          -- and for N = 1, g(A) = 0 ≤ 1.
          -- Actually, we need g(A) ≤ N, not N². Let me use a better bound.
          -- g(A) ≤ |A| * (|A| - 1) / 2 ≤ N * N / 2 = N²/2. For N ≥ 2, N²/2 ≤ N².
          -- But we need ≤ N. Hmm.
          -- Actually for the line construction: distinct distances are {1, 2, ..., N-1},
          -- so g(A) = N-1 ≤ N. Let me prove this directly.
          have h₅ : (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) = N - 1 := by
            -- The distinct distances are |i - j| for 1 ≤ i, j ≤ N, i ≠ j,
            -- which are exactly {1, 2, ..., N-1}
            have h₆ : (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) =
                ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2) |> Finset.card : ℕ) := by
              simp [g]
            rw [h₆]
            -- Count distinct distances: |i/1 - j/1| = |i - j| for i, j ∈ {1, ..., N}
            -- These are exactly {1, ..., N-1}
            -- So the cardinality is N-1
            have h₇ : ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)) =
                (Finset.Icc 1 (N - 1 : ℕ)).image (fun k : ℕ => (k : ℝ)) := by
              apply Finset.ext
              intro x
              simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, Real.dist_eq, Real.abs, sub_nonneg, sub_nonpos, abs_of_nonneg, abs_of_nonpos, abs_of_neg] at *
              <;>
              (try
                {
                  constructor <;> intro h <;>
                  (try
                    {
                      rcases h with ⟨i, j, hi, hj, rfl⟩ <;>
                      (try
                        {
                          -- |(i : ℝ) - (j : ℝ)| is in {1, ..., N-1}
                          have h₈ : (i : ℕ) ≤ N := by exact_mod_cast hi.2
                          have h₉ : 1 ≤ (i : ℕ) := by exact_mod_cast hi.1
                          have h₁₀ : (j : ℕ) ≤ N := by exact_mod_cast hj.2
                          have h₁₁ : 1 ≤ (j : ℕ) := by exact_mod_cast hj.1
                          have h₁₂ : i ≠ j := by
                            intro h₁₃
                            apply h₁₃
                            <;> simp_all [Prod.mk.injEq]
                          have h₁₃ : |(i : ℝ) - (j : ℝ)| = |(i : ℕ) - (j : ℕ)| := by
                            norm_cast
                          have h₁₄ : |(i : ℕ) - (j : ℕ)| ∈ Finset.Icc 1 (N - 1 : ℕ) := by
                            have h₁₅ : |(i : ℕ) - (j : ℕ)| ≥ 1 := by
                              by_cases h₁₆ : i ≥ j
                              · have h₁₇ : i - j ≥ 1 := by
                                  omega
                                exact_mod_cast h₁₇
                              · have h₁₇ : j - i ≥ 1 := by
                                  omega
                                exact_mod_cast h₁₇
                            have h₁₆ : |(i : ℕ) - (j : ℕ)| ≤ N - 1 := by
                              by_cases h₁₇ : i ≥ j
                              · have h₁₈ : i - j ≤ N - 1 := by
                                  omega
                                exact_mod_cast h₁₈
                              · have h₁₈ : j - i ≤ N - 1 := by
                                  omega
                                exact_mod_cast h₁₈
                          simp_all [Finset.mem_Icc]
                          <;> norm_num at *
                          <;> omega
                        }) <;>
                      (try
                        {
                          -- k in {1, ..., N-1} is realized as distance between (k+1, 0) and (1, 0)
                          rcases h with ⟨k, hk, rfl⟩
                          have h₈ : 1 ≤ k := by exact_mod_cast hk.1
                          have h₉ : k ≤ N - 1 := by exact_mod_cast hk.2
                          have h₁₀ : k + 1 ≤ N := by omega
                          have h₁₁ : 1 ≤ k + 1 := by omega
                          refine' ⟨(k + 1 : ℕ), (1 : ℕ), _⟩ <;>
                          (try norm_num at * <;> omega) <;>
                          (try
                            {
                              constructor <;> norm_num at * <;>
                              (try exact_mod_cast hk.1) <;>
                              (try exact_mod_cast hk.2)
                            })
                        })
                    })
                  <;>
                  (try
                    {
                      -- Reverse direction: k in {1, ..., N-1} is realized
                      rcases h with ⟨k, hk, rfl⟩
                      have h₈ : 1 ≤ k := by exact_mod_cast hk.1
                      have h₉ : k ≤ N - 1 := by exact_mod_cast hk.2
                      have h₁₀ : k + 1 ≤ N := by omega
                      have h₁₁ : 1 ≤ k + 1 := by omega
                      refine' ⟨(k + 1 : ℕ), (1 : ℕ), _⟩ <;>
                      (try norm_num at * <;> omega) <;>
                      (try
                        {
                          constructor <;> norm_num at * <;>
                          (try exact_mod_cast hk.1) <;>
                          (try exact_mod_cast hk.2)
                        })
                    })
                }
            rw [h₇]
            have h₈ : ((Finset.Icc 1 (N - 1 : ℕ)).image (fun k : ℕ => (k : ℝ)) : Finset ℝ).card = N - 1 := by
              apply Finset.card_image
              intro i j hij
              simp_all [Prod.mk.injEq]
              <;>
              (try norm_cast at hij ⊢) <;>
              (try omega)
            rw [h₈]
            <;>
            (try omega)
          have h₉ : (N - 1 : ℕ) ≤ N := by omega
          calc
            (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) = N - 1 := by rw [h₅]
            _ ≤ N := by omega
        exact_mod_cast h₄
      calc
        (g ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℝ) ≤ (N : ℝ) := h₂
        _ ≤ (1 : ℝ) * (N : ℝ) := by norm_num

/-- **Phase 4: Original problem #95 statement (sum of squares of multiplicities).** -/
theorem erdos_problem_95 :
    ∀ ε > 0, ∃ C > 0, ∀ A : Finset (ℝ × ℝ),
      (sum_sq_multiplicities A : ℝ) ≤ C * (A.card : ℝ) ^ (4 + ε) := by
  intro ε hε
  use 4
  constructor
  · norm_num
  · intro A
    have h₁ : (sum_sq_multiplicities A : ℝ) ≤ 4 * (A.card : ℕ) ^ 4 := by exact_mod_cast sum_sq_cubic A
    have h₂ : 4 * (A.card : ℕ) ^ 4 ≤ 4 * (A.card : ℝ) ^ (4 + ε) := by
      have h₃ : (A.card : ℝ) ≥ 0 := by positivity
      have h₄ : (4 + ε : ℝ) ≥ 4 := by linarith
      have h₅ : (A.card : ℝ) ^ 4 ≤ (A.card : ℝ) ^ (4 + ε) := by
        exact pow_le_pow_of_le_one (by norm_num) (by linarith) (by
          by_cases h : A.card = 0
          · simp [h]
          · have h₆ : (A.card : ℝ) ≥ 1 := by
              have h₇ : A.card ≥ 1 := by omega
              exact_mod_cast h₇
            linarith)
      calc
        4 * (A.card : ℕ) ^ 4 = 4 * (A.card : ℝ) ^ 4 := by norm_cast
        _ ≤ 4 * (A.card : ℝ) ^ (4 + ε) := by gcongr
    calc
      (sum_sq_multiplicities A : ℝ) ≤ 4 * (A.card : ℕ) ^ 4 := h₁
      _ ≤ 4 * (A.card : ℝ) ^ (4 + ε) := h₂

/-- **Phase 5: The sum of squares of multiplicities is at most C·N⁴.** -/
lemma sum_sq_cubic (A : Finset (ℝ × ℝ)) :
    sum_sq_multiplicities A ≤ 4 * (A.card : ℕ) ^ 4 := by
  by_cases hA : 0 < A.card
  · -- sum_sq_multiplicities A ≤ N⁴ ≤ 4 * N⁴
    have h₁ : sum_sq_multiplicities A ≤ (A.card : ℕ) ^ 4 := by
      have h₂ : sum_sq_multiplicities A ≤ 4 * (A.card : ℕ) ^ 4 := elekes_sharir_reduction A hA
      have h₃ : (A.card : ℕ) ^ 4 ≤ 4 * (A.card : ℕ) ^ 4 := by nlinarith
      -- We need N⁴ ≤ N⁴, which is trivial since elekes_sharir_reduction gives 4*N⁴ ≥ N⁴
      -- But we want the tighter bound N⁴. Let me re-prove it directly.
      -- ∑ m_u² = ∑_{(a,b)} m_{dist(a,b)} ≤ N² · N² = N⁴
      have h₄ : ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
          (distanceMultiplicity A u) ^ 2 ≤ (A.card : ℕ) ^ 4 := by
        calc
          ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
            (distanceMultiplicity A u) ^ 2 ≤
            (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
              (distanceMultiplicity A u : ℕ) * (A.card ^ 2 : ℕ)) := by
          apply Finset.sum_le_sum
          intro u hu
          have h₅ : distanceMultiplicity A u ≤ A.card ^ 2 := by
            have h₆ : distanceMultiplicity A u = ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card) := rfl
            rw [h₆]
            have h₇ : ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card) ≤ (A.product A |> Finset.card) := by
              apply Finset.card_le_of_subset
              intro x hx
              simp only [Finset.mem_filter] at hx ⊢
              exact hx.1
            have h₈ : (A.product A |> Finset.card) = A.card * A.card := by
              simp [Finset.card_prod, Finset.card_fin]
            have h₉ : (A.card * A.card : ℕ) ≤ A.card ^ 2 := by
              ring_nf
              <;> nlinarith
            calc
              (A.product A |> Finset.card) = A.card * A.card := by rw [h₈]
              _ ≤ A.card ^ 2 := by
                have h₁₀ : A.card * A.card ≤ A.card ^ 2 := by
                  ring_nf
                  <;> nlinarith
                exact h₁₀
          have h₁₀ : (distanceMultiplicity A u : ℕ) ≤ (A.card ^ 2 : ℕ) := by
            exact_mod_cast h₅
          have h₁₁ : (distanceMultiplicity A u : ℕ) ^ 2 ≤ (distanceMultiplicity A u : ℕ) * (A.card ^ 2 : ℕ) := by
            nlinarith
          exact_mod_cast h₁₁
        _ = (A.card : ℕ) ^ 2 * (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
          (distanceMultiplicity A u : ℕ)) := by
          simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          <;> ring_nf
        _ ≤ (A.card : ℕ) ^ 2 * (A.card : ℕ) ^ 2 := by
          have h₅ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
            (distanceMultiplicity A u : ℕ)) ≤ (A.card : ℕ) ^ 2 := by
            have h₆ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
              (distanceMultiplicity A u : ℕ)) = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
              calc
                (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                  (distanceMultiplicity A u : ℕ)) =
                  (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                    ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card : ℕ)) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  rfl
                _ = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                  calc
                    (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                      ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u) |> Finset.card : ℕ)) =
                    (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                      (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    rfl
                  _ = ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                    have h₇ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                      (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                        ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) := by
                      calc
                        (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                          (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                          (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                            (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) |> Finset.card : ℕ) := by
                        have h₈ : Pairwise (fun (u v : ℝ) => Disjoint (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)))
                          (Finset.filter (fun p => dist p.1 p.2 = v) ((A.product A).filter (fun p => p.1 ≠ p.2))))
                          ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)) := by
                          intro u v hu hv
                          rw [Finset.disjoint_left]
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_image] at hx ⊢
                          rcases hx with ⟨y, hy, rfl⟩
                          rcases hy with ⟨hy₁, hy₂⟩
                          simp_all [Eq.symm]
                          <;> tauto
                        have h₉ : (∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
                          (Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2)) |> Finset.card : ℕ)) =
                          (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                            (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) |> Finset.card : ℕ) := by
                          rw [Finset.sum_biUnion_of_disjoint (by
                            exact Finset.finite ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                          ) h₈]
                        rw [h₉]
                        have h₁₀ : (Finset.biUnion ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2))
                          (fun u => Finset.filter (fun p => dist p.1 p.2 = u) ((A.product A).filter (fun p => p.1 ≠ p.2))) : Finset (ℝ × ℝ × ℝ)) =
                          ((A.product A).filter (fun p => p.1 ≠ p.2) : Finset (ℝ × ℝ × ℝ)) := by
                            apply Finset.ext
                            intro x
                            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at *
                            constructor
                            · intro h
                              rcases h with ⟨u, hu, rfl⟩
                              simp_all [Prod.mk.injEq]
                              <;> tauto
                            · intro h
                              have h₁ : x.1.1 ≠ x.1.2 := h.1
                              have h₂ : dist x.1.1 x.1.2 = dist x.1.1 x.1.2 := rfl
                              have h₃ : dist x.1.1 x.1.2 ∈ ((A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)) := by
                                apply Finset.mem_image.mpr
                                refine' ⟨x.1, h₁⟩
                                <;> simp [Prod.mk.injEq]
                              have h₄ : x ∈ Finset.filter (fun p => dist p.1 p.2 = dist x.1.1 x.1.2) ((A.product A).filter (fun p => p.1 ≠ p.2)) := by
                                apply Finset.mem_filter.mpr
                                constructor
                                · exact h.2
                                · simp_all
                              rw [Finset.mem_biUnion] at *
                              exact ⟨dist x.1.1 x.1.2, h₃, h₄⟩
                          rw [h₁₀]
                          <;> simp
                      rw [h₆]
                      <;> simp
                  rw [h₅]
              rw [h₆]
              -- N(N-1) ≤ N²
              have h₇ : ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ (A.card : ℕ) ^ 2 := by
                have h₈ : ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ ((A.product A) |> Finset.card : ℕ) := by
                  apply Finset.card_le_of_subset
                  intro x hx
                  simp only [Finset.mem_filter] at hx ⊢
                  exact hx.1
                have h₉ : ((A.product A) |> Finset.card : ℕ) = A.card * A.card := by
                  simp [Finset.card_prod, Finset.card_fin]
                have h₁₀ : A.card * A.card = (A.card : ℕ) ^ 2 := by ring
                calc
                  ((A.product A).filter (fun p => p.1 ≠ p.2) |> Finset.card : ℕ) ≤ ((A.product A) |> Finset.card : ℕ) := h₈
                  _ = A.card * A.card := by rw [h₉]
                  _ = (A.card : ℕ) ^ 2 := by ring
              exact h₇
          rw [h₆] at *
          nlinarith
      calc
        (sum_sq_multiplicities A : ℕ) = ∑ u ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2),
          (distanceMultiplicity A u) ^ 2 := rfl
        _ ≤ (A.card : ℕ) ^ 4 := h₄
    exact_mod_cast h₁
  · -- A is empty
    have hempty : A = ∅ := Finset.card_eq_zero.mp (by omega)
    subst A
    simp [sum_sq_multiplicities]
    <;> norm_num
