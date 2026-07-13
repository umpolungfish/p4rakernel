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

lemma memo_dfd522320c188c51 : |(-1 - Real.sqrt 5) / 2| = (1 + Real.sqrt 5) / 2 := by
  have h : (-1 - Real.sqrt 5) / 2 < 0 := by
    have h1 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : -1 - Real.sqrt 5 < 0 := by linarith
    exact div_lt_zero h2 (by norm_num)
  rw [abs_of_neg h]
  ring
