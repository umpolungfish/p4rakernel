import Imscribing.Erdos710_unified

open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace Erdos710

/-!
# Erdős 710: unconditional dilation and asymptotic lower envelopes

Unified imscription: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM: ⊢∈≻⋈∋⊡⊣; full carrier SIXTEEN₃.

This module imports only the previously kernel-checked arithmetic core.
It introduces no sieve assumptions, axiom declarations, proof holes, or
hypotheses asserting an unproved asymptotic formula.

The sharp asymptotic equivalent of f remains unproved.  In particular, the
unconditional theorems below must not be represented as a sharp equivalent.
-/

/-- For positive n, the minimal permissible open-interval length is positive. -/
theorem f_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < f n := by
  rcases f_admissible n with ⟨a, _hinj, hrange⟩
  have h := hrange (⟨0, hn⟩ : Fin n)
  omega

/-- Divisibility-preserving dilation.  The right endpoint R(n)=n+f(n)-1
    satisfies R(qm+r) ≥ q R(m) for positive m and q. -/
theorem right_endpoint_dilate (m q r : ℕ)
    (hm : 0 < m) (hq : 0 < q) :
    q * (m + f m - 1) ≤ (q * m + r) + f (q * m + r) - 1 := by
  let n : ℕ := q * m + r
  rcases f_admissible n with ⟨a, ha, hrange⟩
  let idx : Fin m → Fin n := fun i =>
    ⟨q * (i.val + 1) - 1, by
      have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
      have hmul : q * (i.val + 1) ≤ q * m :=
        Nat.mul_le_mul_left q hi
      have hpos : 0 < q * (i.val + 1) :=
        Nat.mul_pos hq (by omega)
      dsimp [n]
      omega⟩
  have hidx (i : Fin m) : (idx i).val + 1 = q * (i.val + 1) := by
    have hpos : 0 < q * (i.val + 1) := Nat.mul_pos hq (by omega)
    dsimp [idx]
    omega
  have hdiv (i : Fin m) : q * (i.val + 1) ∣ a (idx i) := by
    simpa only [hidx i] using (hrange (idx i)).2.2
  have hqdiv (i : Fin m) : q ∣ a (idx i) := by
    exact (dvd_mul_right q (i.val + 1)).trans (hdiv i)
  let b : Fin m → ℕ := fun i => a (idx i) / q
  have hbq (i : Fin m) : q * b i = a (idx i) := by
    dsimp [b]
    exact Nat.mul_div_cancel_left' (hqdiv i)
  have hbinj : Function.Injective b := by
    intro i j hij
    have haij : a (idx i) = a (idx j) := by
      calc
        a (idx i) = q * b i := (hbq i).symm
        _ = q * b j := by rw [hij]
        _ = a (idx j) := hbq j
    have hidxij : idx i = idx j := ha haij
    have hval : (idx i).val = (idx j).val :=
      congrArg (fun z : Fin n => z.val) hidxij
    have hmul : q * (i.val + 1) = q * (j.val + 1) := by
      have hi : 0 < q * (i.val + 1) := Nat.mul_pos hq (by omega)
      have hj : 0 < q * (j.val + 1) := Nat.mul_pos hq (by omega)
      dsimp [idx] at hval
      omega
    have hmul' : (i.val + 1) * q = (j.val + 1) * q := by
      simpa only [Nat.mul_comm] using hmul
    have hv : i.val + 1 = j.val + 1 :=
      Nat.mul_right_cancel hq hmul'
    exact Fin.ext (by omega)
  have hbdiv (i : Fin m) : (i.val + 1) ∣ b i := by
    obtain ⟨w, hw⟩ := hdiv i
    have hqeq : q * b i = q * ((i.val + 1) * w) := by
      calc
        q * b i = a (idx i) := hbq i
        _ = (q * (i.val + 1)) * w := hw
        _ = q * ((i.val + 1) * w) := by ring
    have hbeq : b i = (i.val + 1) * w := by
      apply Nat.mul_right_cancel hq
      simpa only [Nat.mul_comm] using hqeq
    exact ⟨w, hbeq⟩
  have hblo (i : Fin m) : m < b i := by
    have hmul : q * m < q * b i := by
      calc
        q * m ≤ n := by dsimp [n]; omega
        _ < a (idx i) := (hrange (idx i)).1
        _ = q * b i := (hbq i).symm
    exact (Nat.mul_lt_mul_left hq).mp hmul
  let R : ℕ := (n + f n - 1) / q
  have hbhi (i : Fin m) : b i ≤ R := by
    have hle : a (idx i) ≤ n + f n - 1 := by
      have h := (hrange (idx i)).2.1
      omega
    dsimp [b, R]
    exact Nat.div_le_div_right hle
  have hmR : m ≤ R := by
    let i₀ : Fin m := ⟨0, hm⟩
    exact (Nat.le_of_lt (hblo i₀)).trans (hbhi i₀)
  have hshort : HasDivisibleDistinctTuple m m (R - m + 1) := by
    refine ⟨b, hbinj, ?_⟩
    intro i
    refine ⟨hblo i, ?_, hbdiv i⟩
    have hh := hbhi i
    omega
  have hmin : f m ≤ R - m + 1 := Nat.sInf_le hshort
  have hRm : m + f m - 1 ≤ R := by omega
  have hRq : q * R ≤ n + f n - 1 := by
    have hmod := Nat.mod_add_div (n + f n - 1) q
    dsimp [R]
    omega
  have hscale : q * (m + f m - 1) ≤ n + f n - 1 :=
    (Nat.mul_le_mul_left q hRm).trans hRq
  simpa only [n] using hscale

/-- Every finite instance produces a fully unconditional global lower
    envelope for all larger instances. -/
theorem global_pattern_bound (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    n * (m + f m - 1) ≤
      m * (n + f n - 1) + m * (m + f m - 1) := by
  have hq : 0 < n / m := Nat.div_pos hn hm
  have hrepr : n = (n / m) * m + n % m := by
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n m).symm
  have hscale := right_endpoint_dilate m (n / m) (n % m) hm hq
  rw [← hrepr] at hscale
  have hmul :
      m * ((n / m) * (m + f m - 1)) ≤ m * (n + f n - 1) :=
    Nat.mul_le_mul_left m hscale
  have hr : n % m ≤ m := (Nat.mod_lt n hm).le
  have hrem :
      (n % m) * (m + f m - 1) ≤ m * (m + f m - 1) :=
    Nat.mul_le_mul_right (m + f m - 1) hr
  calc
    n * (m + f m - 1) =
        m * ((n / m) * (m + f m - 1)) +
          (n % m) * (m + f m - 1) := by
      conv_lhs => rw [hrepr]
      ring
    _ ≤ m * (n + f n - 1) + m * (m + f m - 1) :=
      Nat.add_le_add hmul hrem

/-- Unconditional 5/4 lower envelope.  There are no hypotheses asking for
    an unproved upper or lower sieve estimate: every positive ε is accepted. -/
theorem eventual_ratio_ge_five_fourths (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 4 : ℝ) - ε ≤ (f n : ℝ) / (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((23 : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  have hnpos : 0 < n := by omega
  have hNle : N ≤ n := by omega
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNle
  have hNlarge : (23 : ℝ) < ε * (N : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hεn : (23 : ℝ) ≤ ε * (n : ℝ) :=
    le_trans (le_of_lt hNlarge)
      (mul_le_mul_of_nonneg_left hnreal (le_of_lt hε))
  have hnat := linear_lower_bound n
  have hreal : (5 : ℝ) * (n : ℝ) ≤
      (4 : ℝ) * (f n : ℝ) + 23 := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- A completely unconditional asymptotic assertion, already implied by
    the verified uniform arithmetic bound: f(n)/n is eventually ≥ 9/8. -/
theorem unconditional_asymptotic_lower_bound :
    ∀ᶠ n : ℕ in atTop, (9 / 8 : ℝ) ≤ (f n : ℝ) / (n : ℝ) :=
  eventually_ratio_ge_nine_eighths

#print axioms right_endpoint_dilate
#print axioms eventual_ratio_ge_five_fourths
#print axioms global_pattern_bound
#print axioms unconditional_asymptotic_lower_bound

end Erdos710
