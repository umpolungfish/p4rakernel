import Imscribing.IUTT
import Mathlib.RingTheory.Radical

/-!
# abc: arithmetic calibration and filtered Closure

Positive coprime triples, the product of distinct prime factors, and real
powers define the arithmetic statement. Log-height calibration identifies
its uniform discrepancy estimate with the filtered estimate. Exponentiation
constructs the arithmetic bound from that estimate.

`ABC_Witness` packages these results with the existing dialetheic Witness
type. Its abc Closure constructor takes `FilteredEstimate` as input.
-/
namespace Imscribing.ABC

noncomputable def radical (n : ℕ) : ℕ := UniqueFactorizationMonoid.radical n
theorem radical_eq_primeFactors (n : ℕ) : radical n = n.primeFactors.prod id := by
  unfold radical UniqueFactorizationMonoid.radical
  rw [UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
theorem radical_pos (n : ℕ) : 0 < radical n := Nat.radical_pos n
theorem radical_one : radical 1 = 1 := UniqueFactorizationMonoid.radical_one
theorem radical_prime {p : ℕ} (hp : Nat.Prime p) : radical p = p := by
  simpa [radical] using UniqueFactorizationMonoid.radical_of_prime hp.prime
theorem radical_power (n k : ℕ) (hk : k ≠ 0) : radical (n ^ k) = radical n :=
  UniqueFactorizationMonoid.radical_pow n hk

structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  sum_eq : a + b = c
  coprime : Nat.Coprime a b

theorem Triple.c_pos (t : Triple) : 0 < t.c := by
  rw [← t.sum_eq]
  exact Nat.add_pos_left t.a_pos _
theorem Triple.pairwise_coprime (t : Triple) :
    Nat.Coprime t.a t.b ∧ Nat.Coprime t.a t.c ∧ Nat.Coprime t.b t.c := by
  rw [← t.sum_eq]
  exact ⟨t.coprime, Nat.coprime_self_add_right.mpr t.coprime,
    Nat.coprime_add_self_right.mpr t.coprime.symm⟩

noncomputable def rad (t : Triple) : ℝ := radical (t.a * t.b * t.c)
theorem rad_pos (t : Triple) : 0 < rad t := by
  unfold rad
  exact_mod_cast radical_pos (t.a * t.b * t.c)
noncomputable def logHeight (t : Triple) : ℝ := Real.log t.c
noncomputable def logRadical (t : Triple) : ℝ := Real.log (rad t)

/-- The usual K_epsilon formulation, with a constant uniform over triples. -/
def Conjecture : Prop := ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
  ∀ t : Triple, (t.c : ℝ) ≤ K * (rad t) ^ (1 + ε)

/-- The same statement spelled out without the Triple structure. -/
def StandardStatement : Prop := ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
  ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + ε)
theorem conjecture_iff_standard : Conjecture ↔ StandardStatement := by
  constructor
  · intro h ε hε
    obtain ⟨K, hK, bound⟩ := h ε hε
    refine ⟨K, hK, ?_⟩
    intro a b c ha hb hs hc
    exact bound ⟨a, b, c, ha, hb, hs, hc⟩
  · intro h ε hε
    obtain ⟨K, hK, bound⟩ := h ε hε
    exact ⟨K, hK, fun t => bound t.a t.b t.c t.a_pos t.b_pos t.sum_eq t.coprime⟩

def LogEstimate : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
  ∀ t : Triple, logHeight t ≤ (1 + ε) * logRadical t + C

theorem bound_iff_log_bound (t : Triple) (ε K : ℝ) (hK : 0 < K) :
    (t.c : ℝ) ≤ K * (rad t) ^ (1 + ε) ↔
      logHeight t ≤ (1 + ε) * logRadical t + Real.log K := by
  have hc : (0 : ℝ) < t.c := by exact_mod_cast t.c_pos
  have hp := Real.rpow_pos_of_pos (rad_pos t) (1 + ε)
  rw [← Real.log_le_log_iff hc (mul_pos hK hp),
    Real.log_mul (ne_of_gt hK) (ne_of_gt hp), Real.log_rpow (rad_pos t)]
  simp only [logHeight, logRadical, add_comm]

/-- The exponentiation step, with the constant K=exp C constructed. -/
theorem conjecture_iff_log_estimate : Conjecture ↔ LogEstimate := by
  constructor
  · intro h ε hε
    obtain ⟨K, hK, bound⟩ := h ε hε
    exact ⟨Real.log K, fun t => (bound_iff_log_bound t ε K hK).mp (bound t)⟩
  · intro h ε hε
    obtain ⟨C, bound⟩ := h ε hε
    refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
    intro t
    apply (bound_iff_log_bound t ε (Real.exp C) (Real.exp_pos C)).mpr
    simpa only [Real.log_exp] using bound t

noncomputable def discrepancy (ε : ℝ) (t : Triple) : ℝ :=
  logHeight t - (1 + ε) * logRadical t
def UniformDiscrepancyBound : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
  ∀ t : Triple, discrepancy ε t ≤ C
theorem log_estimate_iff_discrepancy : LogEstimate ↔ UniformDiscrepancyBound := by
  simp only [LogEstimate, UniformDiscrepancyBound, discrepancy, sub_le_iff_le_add, add_comm]
theorem conjecture_iff_uniform_discrepancy : Conjecture ↔ UniformDiscrepancyBound :=
  conjecture_iff_log_estimate.trans log_estimate_iff_discrepancy

/-! A concrete calibration into IUTT's filtered vector packet. This builds
    the representation; it does not assert a uniform estimate for it. -/
noncomputable def arithmeticPacket (t : Triple) : IUTT.Packet :=
  ![logRadical t, 0, logHeight t / 4]
noncomputable def arithmeticRecord (t : Triple) : IUTT.State × IUTT.Packet :=
  (IUTT.boundedDiscrepancy, arithmeticPacket t)
theorem record_preserves_full_state (t : Triple) :
    (arithmeticRecord t).1 = IUTT.boundedDiscrepancy := rfl
theorem packet_radical_calibration (t : Triple) :
    arithmeticPacket t 0 = logRadical t := rfl
theorem packet_height_calibration (t : Triple) :
    IUTT.weighted (arithmeticPacket t) = logHeight t := by
  norm_num [IUTT.weighted, arithmeticPacket, Fin.sum_univ_succ]
  ring

/-- The arithmetic estimate a filtered construction would still have to prove.
    Placing data into the packet does not establish this proposition. -/
def FilteredEstimate : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
  ∀ t : Triple, IUTT.weighted (arithmeticPacket t) ≤
    (1 + ε) * arithmeticPacket t 0 + C
theorem filtered_estimate_iff_log_estimate : FilteredEstimate ↔ LogEstimate := by
  simp only [FilteredEstimate, LogEstimate, packet_height_calibration,
    packet_radical_calibration]
theorem abc_of_filtered_estimate (h : FilteredEstimate) : Conjecture :=
  conjecture_iff_log_estimate.mpr (filtered_estimate_iff_log_estimate.mp h)

/-- A construction may use any filtered space, provided its scalar observables
    are calibrated to the arithmetic and its uniform estimate is proved. -/
theorem abc_of_calibrated_filtered_bound {α : Type*} (_F : IUTT.Filtration α)
    (encode : Triple → α) (height conductor : α → ℝ)
    (height_calibration : ∀ t, height (encode t) = logHeight t)
    (conductor_calibration : ∀ t, conductor (encode t) = logRadical t)
    (bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ t, height (encode t) ≤ (1 + ε) * conductor (encode t) + C) : Conjecture := by
  apply conjecture_iff_log_estimate.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := bound ε hε
  refine ⟨C, ?_⟩
  intro t
  simpa only [height_calibration, conductor_calibration] using hC t

/-- Regression: this radical is not the constant-one placeholder. -/
theorem radical_216 : radical 216 = 6 := by
  rw [radical_eq_primeFactors]
  norm_num [Nat.primeFactors, Nat.primeFactorsList]
def one_eight_nine : Triple := ⟨1, 8, 9, by decide, by decide, by decide, by decide⟩
theorem example_radical : rad one_eight_nine = 6 := by
  change (radical 72 : ℝ) = 6
  have h : radical 72 = 6 := by
    rw [radical_eq_primeFactors]
    norm_num [Nat.primeFactors, Nat.primeFactorsList]
  rw [h]
  norm_num
theorem naive_radical_bound_fails : ¬ (one_eight_nine.c : ℝ) ≤ rad one_eight_nine := by
  rw [example_radical]
  norm_num [one_eight_nine]

noncomputable def quality (t : Triple) : ℝ := logHeight t / logRadical t

theorem rad_ge_two (t : Triple) : 2 ≤ rad t := by
  have hc : 2 ≤ t.c := by have := t.a_pos; have := t.b_pos; have := t.sum_eq; omega
  have hab : 1 ≤ t.a * t.b := Nat.succ_le_of_lt (Nat.mul_pos t.a_pos t.b_pos)
  have hp : 2 ≤ t.a * t.b * t.c := by
    calc 2 ≤ t.c := hc
         _ = 1 * t.c := by simp
         _ ≤ t.a * t.b * t.c := Nat.mul_le_mul_right t.c hab
  have hr : 2 ≤ radical (t.a * t.b * t.c) := Nat.two_le_radical_iff.mpr hp
  unfold rad
  exact_mod_cast hr

theorem logRadical_ge_log_two (t : Triple) : Real.log 2 ≤ logRadical t :=
  Real.log_le_log (by norm_num) (rad_ge_two t)
theorem logRadical_pos (t : Triple) : 0 < logRadical t :=
  lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (logRadical_ge_log_two t)

/-- ε=1 gives coefficient 2. max C 0 handles either sign of the additive
    constant, so division by log(rad) is bounded in the correct direction. -/
theorem quality_bounded_of_log_estimate (h : LogEstimate) :
    ∃ Q : ℝ, ∀ t : Triple, quality t ≤ Q := by
  obtain ⟨C, hC⟩ := h 1 (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 + max C 0 / Real.log 2, ?_⟩
  intro t
  have hc := hC t
  norm_num at hc
  have correction : max C 0 ≤ (max C 0 / Real.log 2) * logRadical t := by
    calc max C 0 = (max C 0 / Real.log 2) * Real.log 2 := by
           rw [div_mul_cancel₀ _ (ne_of_gt h2)]
         _ ≤ (max C 0 / Real.log 2) * logRadical t :=
           mul_le_mul_of_nonneg_left (logRadical_ge_log_two t)
             (div_nonneg (le_max_right C 0) h2.le)
  unfold quality
  apply (div_le_iff₀ (logRadical_pos t)).mpr
  have := le_max_left C 0
  nlinarith

end Imscribing.ABC
