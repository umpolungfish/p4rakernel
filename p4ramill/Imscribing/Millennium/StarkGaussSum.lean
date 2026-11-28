import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkCharacter
import Imscribing.Millennium.StarkLogRung

/-!
# StarkGaussSum — the Gauss-sum brick

The quadratic Gauss sum τ(χ) = ∑_j χ(j)·exp(2πi·j/con) of the Stark character
of `F₂₀₄₈ = ℚ(√4190205)`. This first part carries the algebraic reindex that the
Dirichlet L-series rung consumes:

* `qchar'_isQuadratic` : the Stark character takes only the values 0, 1, −1;
* `stdAddChar_eq_rootExp` : Mathlib's standard additive character `ZMod con → ℂ`
  agrees with the `rootExp` roots of unity of the Stark log ladder;
* `qchar_dft` : the Fourier reindex — the twisted exponential sum at frequency
  `k` is `gaussSum χ (stdAddChar.mulShift (-k))` (Mathlib, no primitivity needed);
* `qchar_twistedExp` / `qchar_twistedExp_nat` : the same sums in the `rootExp`
  language of the character-filter rung.

The continuation of the brick (primitivity `conductor qchar' = con` via the CRT
certificates u ≡ 1 mod con/p, then the reindex `𝓕 χ k = χ⁻¹(-k)·τ(χ)` and
τ(χ)·conjugate τ(χ) = con by Fourier inversion) attaches here.
-/

open Complex Real Finset
open scoped ComplexConjugate

noncomputable section

namespace Imscribing.Millennium.StarkGaussSum

open Imscribing.Millennium.StarkCharacterD2048
open StarkLogRung
open ZMod

/-! ## Folded helper: the trichotomy of the quadratic character -/

private theorem qchar_trichotomy (x : ZMod con) :
    qchar x = 0 ∨ qchar x = 1 ∨ qchar x = -1 := by
  unfold qchar
  by_cases h : (x.val : ℤ).gcd con = 1
  · rcases jacobiSym.eq_one_or_neg_one h with h1 | h1
    · exact Or.inr (Or.inl (by rw [h1]; norm_num))
    · exact Or.inr (Or.inr (by rw [h1]; norm_num))
  · have h0 : jacobiSym (x.val : ℤ) con = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr h
    exact Or.inl (by rw [h0]; norm_num)

/-- The Stark character is quadratic in Mathlib's sense: values in `{0, 1, -1}`. -/
theorem qchar'_isQuadratic : MulChar.IsQuadratic qchar' :=
  qchar_trichotomy

/-! ## The standard additive character at the roots of unity -/

/-- Mathlib's standard additive character on `ZMod con` is exactly the
`rootExp` root of unity of the Stark log ladder. -/
theorem stdAddChar_eq_rootExp (j : ZMod con) :
    stdAddChar (N := con) j = rootExp j.val con := by
  have hj : ((j.val : ℤ) : ZMod con) = j := by simp
  have h1 := stdAddChar_coe (N := con) (j.val : ℤ)
  rw [hj] at h1
  rw [h1]
  unfold rootExp
  push_cast
  ring_nf

/-! ## The Fourier reindex -/

/-- The Fourier reindex (Mathlib, unconditional): the discrete Fourier
transform of the Stark character at frequency `k` is the Gauss sum against the
shifted additive character. -/
theorem qchar_dft (k : ZMod con) :
    ZMod.dft qchar k = gaussSum qchar' (stdAddChar.mulShift (-k)) :=
  DirichletCharacter.fourierTransform_eq_gaussSum_mulShift qchar' k

/-- The twisted exponential sum at frequency `k`, in the additive-character
language: `∑_j χ(j)·ψ(j·k) = 𝓕 χ (-k)`. -/
theorem qchar_twistedExp (k : ZMod con) :
    ∑ j : ZMod con, qchar j * stdAddChar (N := con) (j * k)
      = ZMod.dft qchar (-k) := by
  rw [ZMod.dft_apply]
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  rw [show (-(j * -k) : ZMod con) = j * k from by ring, smul_eq_mul, mul_comm]

/-- The twisted exponential sum at natural frequency `n + 1` in the `rootExp`
language of the character-filter rung: `∑_j χ(j)·u_j^{n+1} = 𝓕 χ (-(n+1))`. -/
theorem qchar_twistedExp_nat (n : ℕ) :
    ∑ j : ZMod con, qchar j * (rootExp j.val con) ^ (n + 1)
      = ZMod.dft qchar (-((n + 1 : ℕ) : ZMod con)) := by
  rw [ZMod.dft_apply]
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  have h1 : (rootExp j.val con) ^ (n + 1)
      = stdAddChar (N := con) (((n + 1 : ℕ) : ZMod con) * j) := by
    rw [← stdAddChar_eq_rootExp j, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [h1, mul_comm (qchar j) (stdAddChar (N := con) _), mul_neg, neg_neg, smul_eq_mul,
    mul_comm ((n + 1 : ℕ) : ZMod con) j]

/-! ## Primitivity of the Stark character via CRT certificates -/

/-- `con` factors into four distinct primes. -/
theorem con_factorization : con = 3 * 5 * 409 * 683 := by norm_num

/-- Every prime divisor of `con` is one of its four factors. -/
private theorem con_prime_div (p : ℕ) (hpp : p.Prime) (hp : p ∣ con) :
    p = 3 ∨ p = 5 ∨ p = 409 ∨ p = 683 := by
  rw [con_factorization] at hp
  rcases (Nat.Prime.dvd_mul hpp).mp hp with h | h
  · rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul hpp).mp h' with h'' | h''
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h'')
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h''))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h')))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h)))

/-- The CRT certificates: for every prime `p ∣ con` there is an integer `u` that is a
unit mod `con`, congruent to `1` mod `con/p`, and has Stark character value `-1`.
Concretely `u = 1 + (con/p)·k` with `u ≡ aₚ mod p` where `(aₚ | p) = -1`:
`k = 1, 1, 123, 626` for `p = 3, 5, 409, 683`. -/
private theorem exists_certificate (p : ℕ) (hpp : p.Prime) (hp : p ∣ con) :
    ∃ u : ℕ, IsUnit ((u : ZMod con)) ∧ (u : ℕ) ≡ 1 [MOD con / p]
      ∧ qchar' ((u : ZMod con)) = (-1 : ℂ) := by
  rcases con_prime_div p hpp hp with rfl | rfl | rfl | rfl
  · refine ⟨1396736, ?_, ?_, ?_⟩
    · rw [ZMod.isUnit_iff_coprime 1396736 con]; decide
    · decide
    · have hv : ((1396736 : ZMod con)).val = 1396736 := by decide
      have hj : (jacobiSym ((1396736 : ℕ) : ℤ) con : ℤ) = -1 := by norm_num
      calc qchar' ((1396736 : ZMod con))
          = ((jacobiSym (((1396736 : ZMod con)).val : ℤ) con : ℤ) : ℂ) := rfl
        _ = ((jacobiSym ((1396736 : ℕ) : ℤ) con : ℤ) : ℂ) := by rw [hv]
        _ = (-1 : ℂ) := by rw [hj]; norm_num
  · refine ⟨838042, ?_, ?_, ?_⟩
    · rw [ZMod.isUnit_iff_coprime 838042 con]; decide
    · decide
    · have hv : ((838042 : ZMod con)).val = 838042 := by decide
      have hj : (jacobiSym ((838042 : ℕ) : ℤ) con : ℤ) = -1 := by norm_num
      calc qchar' ((838042 : ZMod con))
          = ((jacobiSym (((838042 : ZMod con)).val : ℤ) con : ℤ) : ℂ) := rfl
        _ = ((jacobiSym ((838042 : ℕ) : ℤ) con : ℤ) : ℂ) := by rw [hv]
        _ = (-1 : ℂ) := by rw [hj]; norm_num
  · refine ⟨1260136, ?_, ?_, ?_⟩
    · rw [ZMod.isUnit_iff_coprime 1260136 con]; decide
    · decide
    · have hv : ((1260136 : ZMod con)).val = 1260136 := by decide
      have hj : (jacobiSym ((1260136 : ℕ) : ℤ) con : ℤ) = -1 := by norm_num
      calc qchar' ((1260136 : ZMod con))
          = ((jacobiSym (((1260136 : ZMod con)).val : ℤ) con : ℤ) : ℂ) := rfl
        _ = ((jacobiSym ((1260136 : ℕ) : ℤ) con : ℤ) : ℂ) := by rw [hv]
        _ = (-1 : ℂ) := by rw [hj]; norm_num
  · refine ⟨3840511, ?_, ?_, ?_⟩
    · rw [ZMod.isUnit_iff_coprime 3840511 con]; decide
    · decide
    · have hv : ((3840511 : ZMod con)).val = 3840511 := by decide
      have hj : (jacobiSym ((3840511 : ℕ) : ℤ) con : ℤ) = -1 := by norm_num
      calc qchar' ((3840511 : ZMod con))
          = ((jacobiSym (((3840511 : ZMod con)).val : ℤ) con : ℤ) : ℂ) := rfl
        _ = ((jacobiSym ((3840511 : ℕ) : ℤ) con : ℤ) : ℂ) := by rw [hv]
        _ = (-1 : ℂ) := by rw [hj]; norm_num

/-- For every proper divisor `d ∣ con` there is a prime `p ∣ con` with `d ∣ con/p`. -/
private theorem exists_prime_dividing_quotient (d : ℕ) (hd : d ∣ con) (hlt : d < con) :
    ∃ p : ℕ, p.Prime ∧ p ∣ con ∧ d ∣ con / p := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · obtain ⟨k, hk⟩ := hd
      rw [h0, Nat.zero_mul] at hk
      exact absurd hk con_ne_zero
    · exact h0
  obtain ⟨k, hk⟩ := hd
  have hq : con / d = k := by
    rw [hk]
    exact Nat.mul_div_cancel_left k hd0
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk1
    · have hk0 : k = 0 ∨ k = 1 := by omega
      rcases hk0 with hk0 | hk0
      · rw [hk0, Nat.mul_zero] at hk; exact absurd hk con_ne_zero
      · rw [hk0, Nat.mul_one] at hk; omega
    · exact hk1
  obtain ⟨p, hpp, hpk⟩ := Nat.exists_prime_and_dvd (n := con / d) (by rw [hq]; omega)
  refine ⟨p, hpp, ?_, ?_⟩
  · rw [hk, ← hq]; exact dvd_mul_of_dvd_right hpk d
  · obtain ⟨r, hr⟩ := hpk
    have hcon2 : con = p * (d * r) := by rw [hk, ← hq, hr]; ring
    have hdp : con / p = d * r := by
      rw [hcon2]
      exact Nat.mul_div_cancel_left (d * r) hpp.pos
    rw [hdp]
    exact Nat.dvd_mul_right d r

/-- The Stark character is self-inverse: `χ⁻¹ = χ` (values `0, 1, -1`). -/
private theorem qchar'_inv_self (x : ZMod con) : MulChar.inv qchar' x = qchar' x := by
  have h : MulChar.inv qchar' x = (qchar' x)⁻¹ := MulChar.inv_apply_eq_inv' qchar' x
  rw [h]
  rcases qchar_trichotomy x with h' | h' | h'
  · rw [qchar_apply, h']; norm_num
  · rw [qchar_apply, h', inv_one]
  · rw [qchar_apply, h']; norm_num

/-- From the CRT certificate: no proper divisor of `con` factors `χ` or `χ⁻¹`. -/
private theorem factorsThrough_contra (d : ℕ) (hd : d ∣ con) (hlt : d < con)
    (χ : DirichletCharacter ℂ con)
    (hval : ∀ u : ℕ, IsUnit ((u : ZMod con)) → qchar' ((u : ZMod con)) = (-1 : ℂ) →
      χ ((u : ZMod con)) = (-1 : ℂ)) :
    ¬ DirichletCharacter.FactorsThrough χ d := by
  intro hf
  obtain ⟨p, hpp, hpcon, hdvd⟩ := exists_prime_dividing_quotient d hd hlt
  obtain ⟨u, hu, hmod, hchi⟩ := exists_certificate p hpp hpcon
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at hf
  have hker : ZMod.unitsMap hd hu.unit = 1 := by
    refine Units.ext ?_
    rw [ZMod.unitsMap_val, Units.val_one, IsUnit.unit_spec,
      ZMod.cast_natCast (show d ∣ con from hd) u]
    exact ((ZMod.natCast_eq_natCast_iff u 1 d).mpr (Nat.ModEq.of_dvd hdvd hmod)).trans
      Nat.cast_one
  have h1 := hf hker
  have h2 : χ ((u : ZMod con)) = 1 := by
    have h2' := congrArg Units.val h1
    rw [MulChar.coe_toUnitHom, Units.val_one, IsUnit.unit_spec] at h2'
    exact h2'
  have hneg : χ ((u : ZMod con)) = (-1 : ℂ) := hval u hu hchi
  rw [hneg] at h2
  norm_num at h2

private theorem not_factorsThrough_of_lt (d : ℕ) (hd : d ∣ con) (hlt : d < con) :
    ¬ DirichletCharacter.FactorsThrough qchar' d
      ∧ ¬ DirichletCharacter.FactorsThrough (MulChar.inv qchar') d :=
  ⟨factorsThrough_contra d hd hlt qchar' fun _ _ hchi => hchi,
   factorsThrough_contra d hd hlt (MulChar.inv qchar') fun u _ hchi => by
     rw [qchar'_inv_self ((u : ZMod con))]
     exact hchi⟩

/-- The Stark character is primitive: its conductor is the full level `con`. -/
theorem qchar'_isPrimitive : DirichletCharacter.IsPrimitive qchar' := by
  rcases Nat.lt_or_ge (DirichletCharacter.conductor qchar') con with hlt | hge
  · obtain ⟨hf, _⟩ := not_factorsThrough_of_lt _
      (DirichletCharacter.conductor_dvd_level qchar') hlt
    exact absurd ((DirichletCharacter.mem_conductorSet_iff qchar').mp
      (DirichletCharacter.conductor_mem_conductorSet qchar')) hf
  · exact Nat.le_antisymm (Nat.le_of_dvd con_pos
      (DirichletCharacter.conductor_dvd_level qchar')) hge

/-- The inverse character is primitive as well (proved directly; Mathlib has no
`conductor_inv`). -/
theorem qchar'inv_isPrimitive : DirichletCharacter.IsPrimitive (MulChar.inv qchar') := by
  rcases Nat.lt_or_ge (DirichletCharacter.conductor (MulChar.inv qchar')) con with hlt | hge
  · obtain ⟨_, hf⟩ := not_factorsThrough_of_lt _
      (DirichletCharacter.conductor_dvd_level (MulChar.inv qchar')) hlt
    exact absurd ((DirichletCharacter.mem_conductorSet_iff (MulChar.inv qchar')).mp
      (DirichletCharacter.conductor_mem_conductorSet (MulChar.inv qchar'))) hf
  · exact Nat.le_antisymm (Nat.le_of_dvd con_pos
      (DirichletCharacter.conductor_dvd_level (MulChar.inv qchar'))) hge

/-! ## Values of the inverse character -/

/-- The Stark character is real-valued. -/
private theorem qchar'_conj (x : ZMod con) : conj (qchar' x) = qchar' x := by
  rcases qchar_trichotomy x with h | h | h
  · rw [qchar_apply, h, map_zero]
  · rw [qchar_apply, h, map_one]
  · rw [qchar_apply, h, map_neg, map_one]

/-- The inverse character at the reflected argument is the conjugate:
`χ⁻¹(-a) = conj χ(a)`. -/
private theorem qchar'_inv_neg (a : ZMod con) :
    MulChar.inv qchar' (-a) = conj (qchar' a) := by
  have h1 : qchar' (-1 : ZMod con) = 1 := qchar_neg_one
  rw [qchar'_inv_self, ← neg_one_mul, map_mul, h1, one_mul, qchar'_conj]

/-- The Stark character is even: `χ(-a) = χ(a)`. -/
private theorem qchar'_neg (a : ZMod con) : qchar' (-a) = qchar' a := by
  have h1 : qchar' (-1 : ZMod con) = 1 := qchar_neg_one
  rw [← neg_one_mul, map_mul, h1, one_mul]

/-- Conjugation of the standard additive character is reflection:
`conj ψ(a) = ψ(-a)` (the values are roots of unity). -/
private theorem conj_stdAddChar (a : ZMod con) :
    conj (stdAddChar (N := con) a) = stdAddChar (-a) := by
  rw [stdAddChar_eq_rootExp, stdAddChar_eq_rootExp]
  by_cases h : a = 0
  · subst h
    simp [rootExp]
  · haveI : NeZero (a : ZMod con) := ⟨h⟩
    haveI : NeZero (-(a : ZMod con)) := ⟨by simp [h]⟩
    rw [ZMod.val_neg_of_ne_zero]
    have hconj : conj (2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ)))
        = -(2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ))) := by
      have h2 : conj (2 : ℂ) = 2 := Complex.conj_ofNat 2
      have hpi : conj ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := Complex.conj_ofReal _
      have hI : conj Complex.I = -Complex.I := Complex.conj_I
      have hcast : ∀ n : ℕ, conj ((n : ℂ)) = ((n : ℂ)) := Complex.conj_natCast
      rw [div_eq_mul_inv, map_mul, map_mul, map_mul, map_mul, Complex.conj_inv,
        h2, hpi, hI, hcast, hcast]
      ring
    have hexp : conj (rootExp a.val con)
        = Complex.exp (-(2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ)))) := by
      unfold rootExp
      rw [← Complex.exp_conj, hconj]
    rw [hexp]
    have hval_lt : a.val < con := ZMod.val_lt _
    unfold rootExp
    have hnat : (((con - a.val : ℕ) : ℂ)) = ((con : ℂ) - ((a.val : ℕ) : ℂ)) :=
      Nat.cast_sub hval_lt.le
    rw [hnat]
    have hdiv : (((con : ℂ) - ((a.val : ℕ) : ℂ)) / (con : ℂ))
        = 1 - ((a.val : ℕ) : ℂ) / (con : ℂ) := by field_simp
    rw [hdiv]
    have e2 : 2 * Real.pi * Complex.I * (1 - ((a.val : ℕ) : ℂ) / (con : ℂ))
        = -(2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ)))
          + 2 * Real.pi * Complex.I := by ring
    rw [e2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The Gauss sum of the inverse character equals the Gauss sum itself, and the
Gauss sum is real: `τ(χ⁻¹) = τ(χ) = conj τ(χ)`. -/
private theorem gaussSum_inv_eq_conj :
    gaussSum (MulChar.inv qchar') stdAddChar = conj (gaussSum qchar' stdAddChar) := by
  have hA : gaussSum (MulChar.inv qchar') stdAddChar = gaussSum qchar' stdAddChar := by
    rw [gaussSum, gaussSum]
    exact Finset.sum_congr rfl fun a _ => by rw [qchar'_inv_self a]
  have hB : conj (gaussSum qchar' stdAddChar) = gaussSum qchar' stdAddChar := by
    rw [gaussSum, map_sum]
    have hstep : ∀ a : ZMod con, conj (qchar' a * stdAddChar (N := con) a)
        = qchar' (-a) * stdAddChar (N := con) (-a) := by
      intro a
      rw [map_mul, qchar'_conj a, conj_stdAddChar a, qchar'_neg a]
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    exact Fintype.sum_equiv (Equiv.neg (ZMod con))
      (fun a => qchar' (-a) * stdAddChar (N := con) (-a))
      (fun a => qchar' a * stdAddChar (N := con) a)
      (fun a => rfl)
  exact hA.trans hB.symm

/-- The full Fourier reindex for the primitive Stark character:
`𝓕 χ k = χ⁻¹(-k) · τ(χ)`. -/
theorem qchar_fourierReindex (k : ZMod con) :
    ZMod.dft qchar k = MulChar.inv qchar' (-k) * gaussSum qchar' stdAddChar :=
  DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum qchar'_isPrimitive k

/-- The modulus of the Stark Gauss sum: `τ(χ) · conj τ(χ) = con`, by Fourier
inversion (`dft_dft`) evaluated at `j = 1`. -/
theorem gaussSum_sq_conj :
    gaussSum qchar' stdAddChar * conj (gaussSum qchar' stdAddChar) = (con : ℂ) := by
  have hdd : ZMod.dft (ZMod.dft qchar) 1 = (con : ℂ) • qchar (-1 : ZMod con) := by
    rw [ZMod.dft_dft]
  have hL : ZMod.dft (ZMod.dft qchar) 1
      = gaussSum qchar' stdAddChar * gaussSum (MulChar.inv qchar') stdAddChar := by
    rw [ZMod.dft_apply]
    have h1 : ∀ j : ZMod con, stdAddChar (N := con) (-(j * 1)) • ZMod.dft qchar j
        = (MulChar.inv qchar' (-j) * stdAddChar (N := con) (-j))
          * gaussSum qchar' stdAddChar := by
      intro j
      rw [qchar_fourierReindex, smul_eq_mul, mul_one]
      ring
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h1 j]
    rw [← Finset.sum_mul]
    have h2 : (∑ j : ZMod con, MulChar.inv qchar' (-j) * stdAddChar (N := con) (-j))
        = ∑ a : ZMod con, MulChar.inv qchar' a * stdAddChar a :=
      Fintype.sum_equiv (Equiv.neg (ZMod con)) _ _ (fun a => rfl)
    rw [h2, gaussSum, gaussSum]
    ring
  calc gaussSum qchar' stdAddChar * conj (gaussSum qchar' stdAddChar)
      = ZMod.dft (ZMod.dft qchar) 1 := by
        rw [← gaussSum_inv_eq_conj, ← hL]
    _ = (con : ℂ) • qchar (-1 : ZMod con) := hdd
    _ = (con : ℂ) := by rw [smul_eq_mul, qchar_neg_one, mul_one]

end Imscribing.Millennium.StarkGaussSum

end
