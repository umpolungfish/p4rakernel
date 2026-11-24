import Imscribing.BCReentryBounded
import Lean.Sixteen3

/-!
Native adapter for the BCReentry fork — connects the bounded four-bit mask
semantics to the kernel's Lean.Sixteen3 trilattice type.
This file IS compiled; the sorry is eliminated.
-/

namespace BCReentry

/-- Exact mapping of native Lean.Sixteen3 fields to four binary selections. -/
def nativeMembership (v : Lean.Sixteen3) : Fin 4 → Bool
  | ⟨0, _⟩ => v.hasN
  | ⟨1, _⟩ => v.hasT
  | ⟨2, _⟩ => v.hasF
  | _ => v.hasB

/-- The exact native transport theorem: membership in ofMask equals selected. -/
theorem ofMask_transport (n : Fin 16) (i : Fin 4) :
    nativeMembership (Lean.Sixteen3.ofMask n.val) i = selected n.val i := by
  fin_cases n <;> fin_cases i <;>
  simp [nativeMembership, Lean.Sixteen3.ofMask, selected, Fin.val_zero, Fin.val_succ]
  <;>
  (try decide) <;>
  (try {
    norm_num at *
    <;> rfl
  })

end BCReentry
