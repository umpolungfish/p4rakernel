import Mathlib
import Imscribing.Idempotent15
import Imscribing.IdempotentGcd

namespace Imscribing.Idempotent

/-! ## 7. General square case: ZMod(p²) has only trivial idempotents -/

/-- For any prime p, the only idempotents in ZMod(p²) are 0 and 1. 
Proof: p² ∣ v(v-1). Since p cannot divide both v and v-1, p² must divide one of them. 
Since v < p², this forces v = 0 or v = 1. -/
theorem only_trivial_idem_p_sq (p : ℕ) (hp : Nat.Prime p) (x : ZMod (p ^ 2)) :
    x * x = x → x = 0 ∨ x = 1 := by
  intro h
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  have hvx : (x.val : ZMod (p ^ 2)) = x := ZMod.natCast_zmod_val x
  have hv0 : x.val ≠ 0 := by
    intro hv
    exact hx0 ((ZMod.val_eq_zero x).mp hv)
  have hvpos : 1 ≤ x.val := Nat.pos_of_ne_zero hv0
  have hlt : x.val < p ^ 2 := ZMod.val_lt x
  have hdvd : p ^ 2 ∣ x.val * (x.val - 1) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub hvpos,
      Nat.cast_one, hvx]
    calc x * (x - 1) = x * x - x := by ring
         _ = 0 := by rw [h, sub_self]
  have hcon : Nat.Coprime x.val (x.val - 1) := by
    exact (Nat.coprime_self_sub_right hvpos).mpr (by simp)
  by_cases hpv : p ∣ x.val
  · have hpnot : ¬ p ∣ x.val - 1 := by
      intro hpred
      have hboth := Nat.dvd_gcd hpv hpred
      rw [hcon.gcd_eq_one] at hboth
      exact hp.not_dvd_one hboth
    have hcop : Nat.Coprime (p ^ 2) (x.val - 1) :=
      (hp.coprime_iff_not_dvd.mpr hpnot).pow_left 2
    have hdiv : p ^ 2 ∣ x.val := hcop.dvd_of_dvd_mul_right hdvd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) hdiv
    omega
  · have hcop : Nat.Coprime (p ^ 2) x.val :=
      (hp.coprime_iff_not_dvd.mpr hpv).pow_left 2
    have hdiv : p ^ 2 ∣ x.val - 1 :=
      hcop.dvd_of_dvd_mul_right (by simpa only [mul_comm] using hdvd)
    have hpred : x.val - 1 = 0 := by
      by_contra hn
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
      omega
    have hv1 : x.val = 1 := by omega
    right
    calc x = (x.val : ZMod (p ^ 2)) := hvx.symm
         _ = 1 := by rw [hv1]; simp

/-- Transport a square root of one into an idempotent when two has an inverse.
This is the phase half-return boundary used by the word-native extractor. -/
theorem idem_of_involution_unit_two {R : Type*} [CommRing R]
    (s invTwo : R) (hs : s * s = 1) (hi : 2 * invTwo = 1) :
    ((s + 1) * invTwo) * ((s + 1) * invTwo) = (s + 1) * invTwo := by
  calc
    ((s + 1) * invTwo) * ((s + 1) * invTwo) =
        (s * s + 2 * s + 1) * (invTwo * invTwo) := by ring
    _ = ((s + 1) * invTwo) * (2 * invTwo) := by rw [hs]; ring
    _ = (s + 1) * invTwo := by rw [hi, mul_one]

/-! ## 8. The `IdempotentArev` factoring bridge -/

/-- If `IdempotentArev f` holds, then `f` yields nontrivial idempotents,
which by `idem_gcd_factor` give a nontrivial factor of `p * q`. 
This closes the loop: the Prop definition actually guarantees a factoring algorithm. -/
theorem IdempotentArev_factors (f : ℕ → ℕ) (h : IdempotentArev f) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.gcd (f (p * q)) (p * q) = p ∨ Nat.gcd (f (p * q)) (p * q) = q := by
  -- Extract the properties of the idempotent from the Prop
  have hx := h p q hp hq hpq
  let x : ZMod (p * q) := f (p * q)
  have hx_idem : x * x = x := hx.1
  have hx_ne0 : x ≠ 0 := hx.2.1
  have hx_ne1 : x ≠ 1 := hx.2.2
  
  -- Apply the core factoring bridge from IdempotentGcd
  have hfactor := Imscribing.IdempotentGcd.idem_gcd_factor p q hp hq hpq x hx_idem hx_ne0 hx_ne1
  
  have hval : x.val = (f (p * q)) % (p * q) := by
    exact ZMod.val_natCast (p * q) (f (p * q))
  have hgcd : Nat.gcd (f (p * q)) (p * q) = Nat.gcd x.val (p * q) := by
    calc Nat.gcd (f (p * q)) (p * q) = Nat.gcd (p * q) (f (p * q)) :=
           Nat.gcd_comm _ _
         _ = Nat.gcd (f (p * q) % (p * q)) (p * q) := Nat.gcd_rec _ _
         _ = Nat.gcd x.val (p * q) := by rw [hval]
  rwa [hgcd]

end Imscribing.Idempotent