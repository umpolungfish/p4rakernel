import Init.Data.Nat.Lemmas

namespace Imscribing.Paraconsistent.CertifiedModularResidue

/-- The base, modulus, and positive period belong to one certificate. -/
structure CertifiedModularOrbit where
  base : Nat
  modulus : Nat
  period : Nat
  modulus_ge_two : 2 ≤ modulus
  period_pos : 0 < period
  period_certificate : base ^ period % modulus = 1

/-- Evaluate the requested tick at its residue in the certified orbit. -/
def step (orbit : CertifiedModularOrbit) (tick : Nat) : Nat :=
  orbit.base ^ (tick % orbit.period) % orbit.modulus

/-- Every tick agrees with the unreduced modular power. Minimality of the
certified period is not a premise. -/
theorem step_correct (orbit : CertifiedModularOrbit) (tick : Nat) :
    step orbit tick = orbit.base ^ tick % orbit.modulus := by
  have one_mod : 1 % orbit.modulus = 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) orbit.modulus_ge_two)
  have expanded : orbit.base ^ tick % orbit.modulus =
      orbit.base ^ (tick % orbit.period) % orbit.modulus := by
    calc
      orbit.base ^ tick % orbit.modulus =
          orbit.base ^ (tick % orbit.period + orbit.period * (tick / orbit.period)) % orbit.modulus :=
        congrArg (fun exponent => orbit.base ^ exponent % orbit.modulus)
          (Nat.mod_add_div tick orbit.period).symm
      _ = (orbit.base ^ (tick % orbit.period) *
          (orbit.base ^ orbit.period) ^ (tick / orbit.period)) % orbit.modulus := by
        rw [Nat.pow_add, Nat.pow_mul]
      _ = (orbit.base ^ (tick % orbit.period) % orbit.modulus *
          ((orbit.base ^ orbit.period) ^ (tick / orbit.period) % orbit.modulus)) % orbit.modulus :=
        Nat.mul_mod _ _ _
      _ = (orbit.base ^ (tick % orbit.period) % orbit.modulus *
          (1 ^ (tick / orbit.period) % orbit.modulus)) % orbit.modulus := by
        rw [Nat.pow_mod (orbit.base ^ orbit.period) (tick / orbit.period) orbit.modulus,
          orbit.period_certificate]
      _ = orbit.base ^ (tick % orbit.period) % orbit.modulus := by
        simp [one_mod]
  exact expanded.symm

theorem residue_index_bound (orbit : CertifiedModularOrbit) (tick : Nat) :
    tick % orbit.period < orbit.period :=
  Nat.mod_lt tick orbit.period_pos

theorem same_residue_same_step (orbit : CertifiedModularOrbit) (left right : Nat)
    (h : left % orbit.period = right % orbit.period) :
    step orbit left = step orbit right :=
  congrArg (fun exponent => orbit.base ^ exponent % orbit.modulus) h

theorem period_multiple_preserves_step (orbit : CertifiedModularOrbit) (tick multiple : Nat) :
    step orbit (tick + orbit.period * multiple) = step orbit tick := by
  simp only [step, Nat.add_mul_mod_self_left]

#print axioms step_correct
#print axioms residue_index_bound
#print axioms same_residue_same_step
#print axioms period_multiple_preserves_step

end Imscribing.Paraconsistent.CertifiedModularResidue
