/-
  Imscribing/YangMills/TrivialWightman.lean

  An unconditional strict Wightman theory with gap 1.  The Clay target binds
  `W : WightmanQFT4DStrict Δ_phys` existentially and never relates it to the OS
  data, so a one-dimensional realization suffices for that obligation.
-/
import Mathlib
import Imscribing.YangMills.OSCompletion

set_option maxHeartbeats 8000000

open scoped ComplexOrder
open Complex Real Filter

namespace YangMills


lemma fold_replicate_id (k : ℕ) :
    List.foldr (fun (A : ℂ →L[ℂ] ℂ) acc => A acc) 1
      (List.replicate k (ContinuousLinearMap.id ℂ ℂ)) = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

lemma fold_ofFn_id (k : ℕ) (xs : Fin k → Space4) :
    List.foldr (fun (A : ℂ →L[ℂ] ℂ) acc => A acc) 1
      (List.ofFn (fun _ : Fin k => ContinuousLinearMap.id ℂ ℂ)) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ]
      simpa using ih (fun _ : Fin k => (0 : Space4))

/-- The one-dimensional strict Wightman theory with gap 1. -/
noncomputable def trivialWightman : WightmanQFT4DStrict (1 : ℝ) where
  Δ_pos := by norm_num
  H := ℂ
  Ω_phys := 1
  Ω_unit := by simp
  U := fun _ => ContinuousLinearMap.id ℂ ℂ
  U_one := by rfl
  U_mul := by intro g h; rfl
  U_unitary := by intro g x y; rfl
  U_vac := by intro g; rfl
  U_trans_cont := by intro ψ; exact continuous_const
  T_E := fun _ => ContinuousLinearMap.id ℂ ℂ
  T_E_zero := by rfl
  T_E_add := by intro s t hs ht; rfl
  T_E_sa := by intro t x y ht; rfl
  T_E_contr := by intro t x ht; simp
  T_E_vac := by intro t ht; rfl
  T_E_gap := by
    intro t ht v hv
    have hv0 : v = 0 := by
      -- v ⟂ 1 in ℂ means ⟪v, 1⟫ = 0, i.e. conj(v)*1 = 0
      have hinner : inner ℂ v (1 : ℂ) = 0 := hv
      simpa using hinner
    subst v
    simp
  φ := fun _ => ContinuousLinearMap.id ℂ ℂ
  covariant := by intro g x; rfl
  local_comm := by intro x y h; rfl
  cyclic_dense := by
    have hset :
        {v : ℂ | ∃ (k : ℕ) (xs : Fin k → Space4),
          v = List.foldr (fun A acc => A acc) 1
            (List.ofFn fun i : Fin k => ContinuousLinearMap.id ℂ ℂ)} = ({1} : Set ℂ) := by
      ext v
      constructor
      · rintro ⟨k, xs, rfl⟩
        exact fold_ofFn_id k xs
      · intro hv
        subst v
        exact ⟨0, Fin.elim0, by simp⟩
    rw [hset]
    have hspan : Submodule.span ℂ ({1} : Set ℂ) = ⊤ := by
      refine top_unique ?_
      intro v hv
      have h1 : (1 : ℂ) ∈ Submodule.span ℂ ({1} : Set ℂ) :=
        Submodule.subset_span (Set.mem_singleton 1)
      simpa using (Submodule.smul_mem (Submodule.span ℂ ({1} : Set ℂ)) v h1)
    rw [hspan]
    simp

end YangMills
