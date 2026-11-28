from pathlib import Path


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    assert count == 1, f"{label}: expected 1 match, found {count}"
    return text.replace(old, new, 1)


def patch_closure_transfer(path: Path) -> None:
    text = path.read_text(encoding="utf-8")

    old_pow = """  | k + 1 => by
      rw [pow_succ', Matrix.mul_assoc, pow_mul_assoc_shift A B k, ← Matrix.mul_assoc A B,
        Matrix.mul_assoc A, ← Matrix.mul_assoc B A, ← pow_succ']"""
    new_pow = """  | k + 1 => by
      rw [pow_succ', Matrix.mul_assoc, pow_mul_assoc_shift A B k, Matrix.mul_assoc A B,
        ← Matrix.mul_assoc B A, ← pow_succ']"""
    text = replace_exact(text, old_pow, new_pow, "ClosureTransfer:pow_mul_assoc_shift")

    old_nc = """    (F_tilde * F = 1) ∧
    (F_tilde * J * F = G_inv * Fᴴ * J * F + Z0 * (1 - P) * J * F) ∧
    ((∃ M : Matrix n n ℂ, J * F = F * M) → Z0 * (1 - P) * J * F = 0) := by
  intro P F_tilde
  have hPF : P * F = F := by
    dsimp [P]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [F_tilde]
    rw [Matrix.add_mul, Matrix.mul_assoc G_inv Fᴴ F, hGinv, Matrix.mul_assoc Z0 (1 - P) F,
      Matrix.sub_mul, Matrix.one_mul, hPF, sub_self, Matrix.mul_zero, add_zero]"""
    new_nc = """    (F_tilde * F = (1 : Matrix n n ℂ)) ∧
    (F_tilde * J * F = G_inv * Fᴴ * J * F + Z0 * (1 - P) * J * F) ∧
    ((∃ M : Matrix n n ℂ, J * F = F * M) → Z0 * (1 - P) * J * F = 0) := by
  intro P F_tilde
  have hPF : P * F = F := by
    dsimp [P]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [F_tilde]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hGinv, Matrix.sub_mul, Matrix.one_mul, hPF,
      sub_self, Matrix.mul_zero, add_zero]"""
    text = replace_exact(text, old_nc, new_nc, "ClosureTransfer:noncanonical_dual_correction")

    path.write_text(text, encoding="utf-8")


def patch_four_cube_incidence(path: Path) -> None:
    text = path.read_text(encoding="utf-8")

    old_fin2 = """private lemma fin2_diff_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = 1) :
    a.val = 0 ∧ b.val = 1 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;> norm_num at h ⊢

private lemma fin2_diff_neg_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = -1) :
    a.val = 1 ∧ b.val = 0 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;> norm_num at h ⊢"""
    new_fin2 = """private lemma fin2_diff_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = 1) :
    a.val = 0 ∧ b.val = 1 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    (try norm_num at h) <;> norm_num

private lemma fin2_diff_neg_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = -1) :
    a.val = 1 ∧ b.val = 0 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    (try norm_num at h) <;> norm_num"""
    text = replace_exact(text, old_fin2, new_fin2, "FourCubeIncidence:fin2_diff")

    old_hmix = """      have hmix_s : isMixed3 (edgeTriple s e) := by
        simp only [isMixed3, hamming3, hes, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]"""
    new_hmix = """      have hmix_s : isMixed3 (edgeTriple s e) := by
        simp [isMixed3, hamming3, hes]"""
    text = replace_exact(text, old_hmix, new_hmix, "FourCubeIncidence:hmix_s")

    path.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    patch_closure_transfer(Path("Imscribing/TrilatticeYM/ClosureTransfer.lean"))
    patch_four_cube_incidence(Path("Imscribing/TrilatticeYM/FourCubeIncidence.lean"))
    print("Patched both files successfully.")