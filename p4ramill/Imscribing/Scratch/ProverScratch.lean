import Mathlib
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.dollarSyntax false
set_option linter.style.lambdaSyntax false
set_option linter.style.refine false
set_option linter.style.show false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.nameCheck false
set_option linter.style.docString false
set_option linter.style.header false
set_option linter.style.missingEnd false
set_option linter.style.openClassical false
set_option linter.style.nativeDecide false
set_option linter.style.admit false

theorem memo_d272293ae5778254 (x y : ℕ) : (x + 1) * x / 2 + y ≤ (x + y + 1) * (x + y) / 2 := by
  have h1 : (x + 1) * x / 2 = Nat.choose (x + 1) 2 := by
    rw [Nat.choose_two_right]
    rfl
  have h2 : (x + y + 1) * (x + y) / 2 = Nat.choose (x + y + 1) 2 := by
    rw [Nat.choose_two_right]
    rfl
  rw [h1, h2]
  induction y with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    apply Nat.le_refl
  | succ y' ih =>
    rw [Nat.choose_succ_two_right (x + y' + 1)]
    rw [Nat.add_succ]
    apply Nat.le_trans ih
    rw [Nat.add_assoc]
    apply Nat.le_add_left
