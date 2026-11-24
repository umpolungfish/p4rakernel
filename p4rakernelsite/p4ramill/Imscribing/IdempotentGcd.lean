import Mathlib

namespace Imscribing.IdempotentGcd

/-- If e ≡ 1 (mod p) and q ∣ e, then gcd(e, pq) = q. -/
theorem gcd_crt_idem (p q e : ℕ) (hp : p.Prime) (h1 : e % p = 1) (h2 : q ∣ e) :
    Nat.gcd e (p * q) = q := by
  apply Nat.dvd_antisymm
  · have hcop : Nat.Coprime (Nat.gcd e (p * q)) p := by
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpd
      have hpe : p ∣ e := dvd_trans hpd (Nat.gcd_dvd_left _ _)
      have h0 : e % p = 0 := Nat.mod_eq_zero_of_dvd hpe
      rw [h1] at h0
      exact one_ne_zero h0
    exact hcop.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_gcd h2 (dvd_mul_left q p)

/-- Symmetric form: if f ≡ 1 (mod q) and p ∣ f, then gcd(f, pq) = p. -/
theorem gcd_crt_idem' (p q f : ℕ) (hq : q.Prime) (h1 : f % q = 1) (h2 : p ∣ f) :
    Nat.gcd f (p * q) = p := by
  rw [mul_comm]
  exact gcd_crt_idem q p f hq h1 h2

theorem mod_one_of_dvd_pred (q v : ℕ) (hq : q.Prime) (hv : 1 ≤ v) (h : q ∣ v - 1) :
    v % q = 1 := by
  obtain ⟨k, hk⟩ := h
  have hv' : v = 1 + q * k := by omega
  rw [hv', Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hq.one_lt

/-- Pure ℕ core: if pq ∣ v(v-1), 0 < v < pq, v ≠ 1, then gcd(v, pq) ∈ {p, q}. -/
theorem nat_core (p q v : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hlt : v < p * q) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hdvd : p * q ∣ v * (v - 1)) :
    Nat.gcd v (p * q) = p ∨ Nat.gcd v (p * q) = q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hvpos : 1 ≤ v := Nat.pos_of_ne_zero hv0
  have hpd : p ∣ v * (v - 1) := dvd_trans (dvd_mul_right p q) hdvd
  have hqd : q ∣ v * (v - 1) := dvd_trans (dvd_mul_left q p) hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with hpv | hpv1 <;>
  rcases (Nat.Prime.dvd_mul hq).mp hqd with hqv | hqv1
  · -- p ∣ v and q ∣ v : pq ∣ v, impossible since 0 < v < pq
    exfalso
    have h := hcop.mul_dvd_of_dvd_of_dvd hpv hqv
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) h
    omega
  · -- p ∣ v, v ≡ 1 mod q : gcd = p
    left
    exact gcd_crt_idem' p q v hq (mod_one_of_dvd_pred q v hq hvpos hqv1) hpv
  · -- v ≡ 1 mod p, q ∣ v : gcd = q
    right
    exact gcd_crt_idem p q v hp (mod_one_of_dvd_pred p v hp hvpos hpv1) hqv
  · -- p ∣ v-1 and q ∣ v-1 : pq ∣ v-1, forcing v = 1
    exfalso
    have h := hcop.mul_dvd_of_dvd_of_dvd hpv1 hqv1
    by_cases hz : v - 1 = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h
      omega

/-- MAIN BRIDGE. For distinct primes p, q: every nontrivial idempotent x of
ZMod (p*q) yields a nontrivial factor, gcd(x.val, pq) ∈ {p, q}. -/
theorem idem_gcd_factor (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x : ZMod (p * q)) (hx : x * x = x) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    Nat.gcd x.val (p * q) = p ∨ Nat.gcd x.val (p * q) = q := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hvx : ((x.val : ℕ) : ZMod (p * q)) = x := ZMod.natCast_zmod_val x
  have hlt : x.val < p * q := ZMod.val_lt x
  have hv0 : x.val ≠ 0 := by
    intro h
    apply h0
    exact (ZMod.val_eq_zero x).mp h
  have hv1 : x.val ≠ 1 := by
    intro h
    apply h1
    calc x = ((x.val : ℕ) : ZMod (p * q)) := hvx.symm
      _ = ((1 : ℕ) : ZMod (p * q)) := congrArg (fun n : ℕ => (n : ZMod (p * q))) h
      _ = 1 := Nat.cast_one
  have hvpos : 1 ≤ x.val := Nat.pos_of_ne_zero hv0
  have hdvd : p * q ∣ x.val * (x.val - 1) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub hvpos, Nat.cast_one, hvx]
    have h2 : x * (x - 1) = x * x - x := by ring
    rw [h2, hx, sub_self]
  exact nat_core p q x.val hp hq hpq hlt hv0 hv1 hdvd

/-- Concrete instance: N = 15, x = 10 gives gcd 5. -/
example : Nat.gcd (10 : ZMod 15).val 15 = 5 := by decide

end Imscribing.IdempotentGcd
