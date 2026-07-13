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

lemma memo_cb90341cada25948 (A : Type) [Semigroup A] (x : A) : x * x = x → x * (x * x) = x * x := by
  intro h
  rw [h]
  rfl
