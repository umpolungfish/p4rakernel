import Mathlib

open Finset

namespace Erdos710

def HasIn (n lo hi : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, Set.InjOn a (Icc 1 n : Finset ℕ) ∧
    ∀ k ∈ Icc 1 n, lo < a k ∧ a k < hi ∧ k ∣ a k

noncomputable def f (n : ℕ) : ℕ := sInf {L | HasIn n n (n + L)}

theorem hasIn_mono_hi {n lo hi hi' : ℕ} (h : hi ≤ hi') (H : HasIn n lo hi) :
    HasIn n lo hi' := by
  obtain ⟨a, ha, h2⟩ := H
  exact ⟨a, ha, fun k hk => ⟨(h2 k hk).1, lt_of_lt_of_le (h2 k hk).2.1 h,
    (h2 k hk).2.2⟩⟩

theorem hasIn_mono_lo {n lo lo' hi : ℕ} (h : lo ≤ lo') (H : HasIn n lo' hi) :
    HasIn n lo hi := by
  obtain ⟨a, ha, h2⟩ := H
  exact ⟨a, ha, fun k hk => ⟨lt_of_le_of_lt h (h2 k hk).1, (h2 k hk).2⟩⟩

theorem tuple_trivial (n : ℕ) : HasIn n n (n + (n ^ 2 + 1)) := by
  refine ⟨fun k => k * (n + 1), ?_, ?_⟩
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) hxy
  · intro k hk
    rw [mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨?_, ?_, dvd_mul_right _ _⟩
    · nlinarith
    · nlinarith

theorem hasIn_f (n : ℕ) : HasIn n n (n + f n) :=
  Nat.sInf_mem (s := {L | HasIn n n (n + L)}) ⟨_, tuple_trivial n⟩

theorem f_le_of_hasIn {m hi : ℕ} (hm : m ≤ hi) (H : HasIn m m hi) :
    f m ≤ hi - m := by
  apply Nat.sInf_le
  have : m + (hi - m) = hi := by omega
  simpa [this] using H

/-! ## Erdős–Pomerance Lemma 1: a smooth Hall violator -/

/-- `a` has no prime factor exceeding `y`. -/
def Smooth (y a : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ a → p ≤ y

open Classical in
/-- If there are more `y`-smooth `a ∈ (nk/y, n]` than `y`-smooth `b ∈ (n, nk]`,
no matching of `{1..n}` into `(n, nk]` with `a ∣ b_a` exists. -/
theorem smooth_violator {n k y : ℕ}
    (h : ((Ioc n (n * k)).filter (Smooth y)).card <
      ((Icc 1 n).filter (fun a => n * k < a * y ∧ Smooth y a)).card) :
    ¬ HasIn n n (n * k + 1) := by
  rintro ⟨a, ha, hmem⟩
  refine absurd h (not_lt.mpr ?_)
  apply Finset.card_le_card_of_injOn a
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hjn⟩, hjy, hjs⟩ := hj
    have hjI : j ∈ Icc 1 n := mem_Icc.mpr ⟨hj1, hjn⟩
    obtain ⟨hl, hr, hd⟩ := hmem j hjI
    obtain ⟨c, hc⟩ := hd
    have hcy : c < y := by
      by_contra hcy
      push_neg at hcy
      have h1 : j * y ≤ j * c := Nat.mul_le_mul_left j hcy
      rw [hc] at hr
      omega
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc
        omega
      · exact h0
    change a j ∈ (Ioc n (n * k)).filter (Smooth y)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hl, by omega⟩, ?_⟩
    intro p hp hpd
    rw [hc] at hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h1 | h1
    · exact hjs p hp h1
    · exact le_of_lt (lt_of_le_of_lt (Nat.le_of_dvd hcpos h1) hcy)
  · intro x hx z hz hxz
    have hx' : x ∈ Icc 1 n := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
    have hz' : z ∈ Icc 1 n := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).1
    exact ha hx' hz' hxz

open Classical in
/-- Consequence for `f`: the violator forces `n + f n > n k`. -/
theorem nk_lt_add_f {n k y : ℕ}
    (h : ((Ioc n (n * k)).filter (Smooth y)).card <
      ((Icc 1 n).filter (fun a => n * k < a * y ∧ Smooth y a)).card) :
    n * k < n + f n := by
  by_contra hge
  push_neg at hge
  exact smooth_violator h (hasIn_mono_hi (by omega) (hasIn_f n))

/-! ## The scaling step (Theorem 2 from Lemma 2) -/

theorem scale {n m q lo hi lo' hi' : ℕ} (hq : 0 < q) (hmq : m * q ≤ n)
    (hlo : q * lo' ≤ lo) (hhi : hi ≤ q * hi') (H : HasIn n lo hi) :
    HasIn m lo' hi' := by
  obtain ⟨a, ha, h⟩ := H
  have mem : ∀ i ∈ Icc 1 m, i * q ∈ Icc 1 n := by
    intro i hi_
    rw [mem_Icc] at hi_ ⊢
    refine ⟨Nat.mul_pos hi_.1 hq, ?_⟩
    exact le_trans (Nat.mul_le_mul_right q hi_.2) hmq
  have hdvd : ∀ i ∈ Icc 1 m, q ∣ a (i * q) := fun i hi_ =>
    dvd_trans (dvd_mul_left q i) (h _ (mem i hi_)).2.2
  refine ⟨fun i => a (i * q) / q, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ Icc 1 m := hx
    have hy' : y ∈ Icc 1 m := hy
    obtain ⟨c, hc⟩ := hdvd x hx'
    obtain ⟨d, hd⟩ := hdvd y hy'
    simp only [hc, hd, Nat.mul_div_cancel_left c hq,
      Nat.mul_div_cancel_left d hq] at hxy
    have h2 : a (x * q) = a (y * q) := by rw [hc, hd, hxy]
    have h3 := ha (mem x hx') (mem y hy') h2
    exact Nat.eq_of_mul_eq_mul_right hq h3
  · intro i hi_
    obtain ⟨h1, h2, h3⟩ := h _ (mem i hi_)
    obtain ⟨c, hc⟩ := hdvd i hi_
    simp only [hc, Nat.mul_div_cancel_left c hq]
    refine ⟨?_, ?_, ?_⟩
    · rw [hc] at h1
      exact lt_of_mul_lt_mul_left (lt_of_le_of_lt hlo h1) (Nat.zero_le q)
    · rw [hc] at h2
      exact lt_of_mul_lt_mul_left (lt_of_lt_of_le h2 hhi) (Nat.zero_le q)
    · rw [hc, mul_comm i q] at h3
      exact (Nat.mul_dvd_mul_iff_left hq).mp h3

/-- Endpoint form: with `E x = x + f x`, `m * q ≤ n` gives
`E m ≤ ⌈E n / q⌉`, i.e. `E m ≤ (E n + q - 1) / q`. -/
theorem scale_endpoint {n m q : ℕ} (hq : 0 < q) (hm : 1 ≤ m)
    (hmq : m * q ≤ n) :
    m + f m ≤ (n + f n + q - 1) / q := by
  set E := n + f n with hE
  set d := (E + q - 1) / q with hd
  have h1 := Nat.div_add_mod (E + q - 1) q
  have h2 := Nat.mod_lt (E + q - 1) hq
  have hhi : E ≤ q * d := by
    rw [← hd] at h1
    generalize (E + q - 1) % q = r at h1 h2
    generalize q * d = t at h1 ⊢
    omega
  have hlo : q * m ≤ n := by rw [mul_comm]; exact hmq
  have H := scale (lo' := m) (hi' := d) hq hmq hlo hhi (hasIn_f n)
  have hmd : m ≤ d := by
    obtain ⟨a, _, hh⟩ := H
    have h1m : 1 ∈ Icc 1 m := mem_Icc.mpr ⟨le_refl 1, hm⟩
    obtain ⟨hl, hr, _⟩ := hh 1 h1m
    omega
  have := f_le_of_hasIn hmd (hasIn_mono_lo (le_refl m) H)
  omega

/-! ## The remaining analytic input, as a statement -/

/-- Erdős–Pomerance Lemma 2 (de Bruijn smooth-number estimate): for every
`ε > 0` and all large `z` there is `m ∈ [z, z^(1+ε)]` with
`f m ≥ (1-ε)(2/√e) m √(log m / log log m)`. NOT proved here. -/
def Lemma2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z → ∃ m : ℕ,
    z ≤ m ∧ (m : ℝ) ≤ z ^ (1 + ε) ∧
    (1 - ε) * (2 / Real.sqrt (Real.exp 1)) * m *
      Real.sqrt (Real.log m / Real.log (Real.log m)) ≤ f m

end Erdos710

#print axioms Erdos710.nk_lt_add_f
#print axioms Erdos710.scale_endpoint
