/-
  Imscribing/YangMills/ContinuumDecomposition.lean

  Atomic decomposition of the strict continuum Clay target.  Rather than
  building one monolithic theory, each field obligation of
  `OsterwalderSchrader4DStrict` is isolated and traced to the strong-coupling
  thermodynamic limit stored in `canonicalThermoData`.

  Path B (`canonicalSContB`) carries Space4 translation invariance but its
  base point `xs 0` breaks permutation symmetry.  Path C below replaces that
  base point by the centroid, which is permutation invariant and translation
  covariant, so a single Schwinger function carries both atomic obligations.
-/
import Mathlib
import Imscribing.YangMills.ContinuumClosure

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open Filter
open scoped BigOperators

namespace YangMills

/-! ### Centroid embedding (Path C) -/

/-- Centroid of a finite family of spacetime points. -/
noncomputable def space4Centroid (n : ℕ) [NeZero n] (xs : Fin n → Space4) : Space4 :=
  fun j => (∑ k : Fin n, xs k j) / (n : ℝ)

/-- Path C embedding: each point is embedded relative to the centroid. -/
noncomputable def canonLoopCent (n : ℕ) [NeZero n] (xs : Fin n → Space4) : Fin n → Loop4DZ :=
  fun i => canonicalLoop4DZ (fun j => xs i j - space4Centroid n xs j)

/-- Path C continuum Schwinger function. -/
noncomputable def canonicalSContC (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) [NeZero n] (xs : Fin n → Space4) : ℂ :=
  canonicalS_inf N hN n (canonLoopCent n xs)

/-! ### Atomic obligation: permutation symmetry -/

theorem canonicalSContC_perm (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) [NeZero n] (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4) :
    canonicalSContC N hN n (fun i => xs (σ i)) = canonicalSContC N hN n xs := by
  unfold canonicalSContC canonLoopCent space4Centroid
  have hfam :
      (fun i => canonicalLoop4DZ (fun j =>
          xs (σ i) j - (∑ k : Fin n, xs (σ k) j) / (n : ℝ))) =
      (fun i => canonicalLoop4DZ (fun j =>
          xs (σ i) j - (∑ k : Fin n, xs k j) / (n : ℝ))) := by
    funext i
    congr 1
    funext j
    congr 1
    exact congrArg (fun t : ℝ => t / (n : ℝ))
      (Fintype.sum_equiv σ (fun k : Fin n => xs (σ k) j) (fun k : Fin n => xs k j)
        (fun _ => rfl))
  rw [hfam]
  exact (Classical.choose_spec (Classical.choose_spec (canonicalThermoData N hN))).2.2.2.1 n σ
    (fun i => canonicalLoop4DZ (fun j => xs i j - (∑ k : Fin n, xs k j) / (n : ℝ)))

/-! ### Atomic obligation: Space4 translation invariance -/

theorem space4Centroid_trans (n : ℕ) [NeZero n] (a : Space4) (xs : Fin n → Space4) :
    space4Centroid n (fun i => fun j => xs i j + a j) =
      fun j => space4Centroid n xs j + a j := by
  funext j
  unfold space4Centroid
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp

theorem canonicalSContC_trans (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) [NeZero n] (a : Space4) (xs : Fin n → Space4) :
    canonicalSContC N hN n (fun i => fun j => xs i j + a j) = canonicalSContC N hN n xs := by
  unfold canonicalSContC canonLoopCent
  have hfam :
      (fun i => canonicalLoop4DZ (fun j =>
          (xs i j + a j) - space4Centroid n (fun i => fun j => xs i j + a j) j)) =
      (fun i => canonicalLoop4DZ (fun j => xs i j - space4Centroid n xs j)) := by
    funext i
    congr 1
    funext j
    rw [space4Centroid_trans]
    ring
  rw [hfam]

#print axioms canonicalSContC_perm
#print axioms canonicalSContC_trans

end YangMills
