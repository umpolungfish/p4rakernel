import Imscribing.Millennium.SourceBraidTapeReturn
import Imscribing.Millennium.SourceBraidSICContraction

/-! The twofold-return selector is a polynomial in the source return Gram.
Source addresses remain banked. The polynomial itself uses no chosen address. -/
namespace Imscribing.SourceBraidPrimeArmProjection

noncomputable def fibreCount (K : Type*) [Semiring K] [Fintype K] (r : K) : ℕ := by
  classical
  exact Fintype.card {x : K // x^2 = r}

theorem field_fibre_zero (K : Type*) [Field K] [Fintype K] :
    fibreCount K 0 = 1 := by
  classical
  simp [fibreCount, sq_eq_zero_iff]

theorem field_fibre_nonzero (K : Type*) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (r : K) (hr : r ≠ 0) :
    fibreCount K r = 0 ∨ fibreCount K r = 2 := by
  classical
  by_cases hex : ∃ x : K, x^2 = r
  · obtain ⟨x,hx⟩ := hex
    have hx0 : x ≠ 0 := by intro h; subst x; simp at hx; exact hr hx.symm
    have hxn : x ≠ -x := by
      intro h
      have hm : (2 : K)*x = 0 := by linear_combination h
      exact hx0 ((mul_eq_zero.mp hm).resolve_left h2)
    right
    have hs : (Finset.univ.filter (fun y : K => y^2=r)) = {x,-x} := by
      ext y
      simp [← hx, sq_eq_sq_iff_eq_or_eq_neg]
    simp only [fibreCount, Fintype.card_subtype]
    rw [hs]
    simp [hxn]
  · left
    have hn : ∀ x : K, ¬x^2=r := by simpa using hex
    simp [fibreCount, Fintype.card_subtype, hn]

noncomputable def fibreCRT {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] (φ : R ≃+* A × B) (r : R) :
    {x : R // x^2=r} ≃
      ({a : A // a^2=(φ r).1} × {b : B // b^2=(φ r).2}) where
  toFun x :=
    (⟨(φ x.val).1, by simpa using congrArg (fun z => (φ z).1) x.property⟩,
     ⟨(φ x.val).2, by simpa using congrArg (fun z => (φ z).2) x.property⟩)
  invFun ab := ⟨φ.symm (ab.1.val,ab.2.val), by
    apply φ.injective
    simp only [map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk]
    exact Prod.ext ab.1.property ab.2.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro ab; apply Prod.ext <;> apply Subtype.ext <;> simp

theorem fibre_count_CRT {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Fintype R] [Fintype A] [Fintype B] (φ : R ≃+* A × B) (r : R) :
    fibreCount R r = fibreCount A (φ r).1 * fibreCount B (φ r).2 := by
  classical
  simpa [fibreCount, Fintype.card_prod] using Fintype.card_congr (fibreCRT φ r)

theorem semiprime_zero_fibre (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) : fibreCount (ZMod (p*q)) 0 = 1 := by
  rw [fibre_count_CRT (ZMod.chineseRemainder hpq)]
  simp [field_fibre_zero]

theorem semiprime_nonzero_fibre (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (hp2 : (2 : ZMod p) ≠ 0)
    (hq2 : (2 : ZMod q) ≠ 0) (r : ZMod (p*q)) (hr : r ≠ 0) :
    fibreCount (ZMod (p*q)) r = 0 ∨ fibreCount (ZMod (p*q)) r = 2 ∨
      fibreCount (ZMod (p*q)) r = 4 := by
  let φ := ZMod.chineseRemainder hpq
  have hn : (φ r).1 ≠ 0 ∨ (φ r).2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hr
    apply φ.injective
    have hz : φ r = ((0 : ZMod p), (0 : ZMod q)) := Prod.ext h.1 h.2
    exact hz.trans (map_zero φ).symm
  rw [fibre_count_CRT φ r]
  by_cases ha : (φ r).1 = 0
  · rw [ha, field_fibre_zero]
    have hb := hn.resolve_left (by simpa using ha)
    rcases field_fibre_nonzero (ZMod q) hq2 (φ r).2 hb with h | h <;> simp [h]
  · have hp := field_fibre_nonzero (ZMod p) hp2 (φ r).1 ha
    by_cases hb : (φ r).2 = 0
    · rw [hb, field_fibre_zero]
      rcases hp with h | h <;> simp [h]
    · have hq := field_fibre_nonzero (ZMod q) hq2 (φ r).2 hb
      rcases hp with h | h <;> rcases hq with j | j <;> simp [h,j]

/-- E is the known source-zero coordinate projector, not the kernel of G. -/
noncomputable def primeArmOperator {Y : Type*} [Fintype Y]
    (G E : Matrix Y Y ℚ) : Matrix Y Y ℚ :=
  (1/4 : ℚ) • ((4 : ℚ) • G - G*G - (3 : ℚ) • E)

theorem selector_scalar (g : ℚ) (isZero : Prop) [Decidable isZero]
    (hzero : isZero → g=1)
    (hlive : ¬isZero → g=0 ∨ g=2 ∨ g=4) :
    (4*g-g*g-3*(if isZero then 1 else 0))/4 = if g=2 then 1 else 0 := by
  by_cases h : isZero
  · rw [hzero h]
    norm_num [h]
  · rcases hlive h with hg | hg | hg <;> rw [hg] <;> norm_num [h]

theorem primeArm_diagonal {Y : Type*} [Fintype Y] [DecidableEq Y]
    (g : Y → ℚ) (z : Y) :
    primeArmOperator (Matrix.diagonal g)
      (Matrix.diagonal (fun y => if y=z then 1 else 0)) =
    Matrix.diagonal (fun y => (4*g y-g y*g y-3*(if y=z then 1 else 0))/4) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [primeArmOperator, Matrix.diagonal_mul_diagonal, Matrix.smul_apply]
    ring
  · simp [primeArmOperator, Matrix.diagonal_mul_diagonal, Matrix.smul_apply, h]

theorem primeArm_projects {Y : Type*} [Fintype Y] [DecidableEq Y]
    (g : Y → ℚ) (z : Y) (hz : g z=1)
    (hlive : ∀ y, y ≠ z → g y=0 ∨ g y=2 ∨ g y=4) :
    primeArmOperator (Matrix.diagonal g)
      (Matrix.diagonal (fun y => if y=z then 1 else 0)) =
    Matrix.diagonal (fun y => if g y=2 then 1 else 0) := by
  rw [primeArm_diagonal]
  congr 1
  funext y
  exact selector_scalar (g y) (y=z) (by intro h; simpa [h] using hz) (hlive y)

theorem sum_fibre_counts (K : Type*) [Semiring K] [Fintype K] :
    (∑ r : K, fibreCount K r) = Fintype.card K := by
  classical
  unfold fibreCount
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : K => x^2))

theorem sum_square_fibre_counts (K : Type*) [Semiring K] [Fintype K] :
    (∑ r : K, (fibreCount K r)^2) =
      Fintype.card (Imscribing.SourceBraidSquareCollision.SquarePairs K) := by
  classical
  simpa [fibreCount, Imscribing.SourceBraidSquareCollision.SquarePairs] using
    (Imscribing.SourceBraidSquareCollision.collision_count_as_fibres (fun x : K => x^2)).symm

noncomputable def sourceGram (K : Type*) [Semiring K] [Fintype K]
    [DecidableEq K] : Matrix K K ℚ :=
  Matrix.diagonal (fun r => (fibreCount K r : ℚ))

noncomputable def sourceZero (K : Type*) [Semiring K] [Fintype K]
    [DecidableEq K] : Matrix K K ℚ :=
  Matrix.diagonal (fun r => if r=0 then 1 else 0)

theorem sourceGram_trace (K : Type*) [Semiring K] [Fintype K] [DecidableEq K] :
    Matrix.trace (sourceGram K) = (Fintype.card K : ℚ) := by
  classical
  simp only [sourceGram, Matrix.trace_diagonal]
  exact_mod_cast sum_fibre_counts K

theorem sourceGram_trace_square (K : Type*) [Semiring K] [Fintype K] [DecidableEq K] :
    Matrix.trace (sourceGram K * sourceGram K) =
      (Fintype.card (Imscribing.SourceBraidSquareCollision.SquarePairs K) : ℚ) := by
  classical
  simp only [sourceGram, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have h := sum_square_fibre_counts K
  simp only [pow_two] at h
  exact_mod_cast h

theorem sourceZero_trace (K : Type*) [Semiring K] [Fintype K] [DecidableEq K] :
    Matrix.trace (sourceZero K) = 1 := by
  classical
  simp [sourceZero]

theorem trace_primeArm {Y : Type*} [Fintype Y] (G E : Matrix Y Y ℚ) :
    4*Matrix.trace (primeArmOperator G E) =
      4*Matrix.trace G - Matrix.trace (G*G) - 3*Matrix.trace E := by
  simp only [primeArmOperator, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  ring

theorem semiprime_primeArm_trace (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (hp2 : (2 : ZMod p) ≠ 0)
    (hq2 : (2 : ZMod q) ≠ 0) :
    Matrix.trace (primeArmOperator (sourceGram (ZMod (p*q)))
      (sourceZero (ZMod (p*q)))) = ((p : ℚ)+q-2)/2 := by
  have h := trace_primeArm (sourceGram (ZMod (p*q))) (sourceZero (ZMod (p*q)))
  rw [sourceGram_trace, sourceGram_trace_square, sourceZero_trace, ZMod.card] at h
  have hC := Imscribing.SourceBraidSquareCollision.semiprime_collision_card p q hpq hp2 hq2
  have hCQ : (Fintype.card (Imscribing.SourceBraidSquareCollision.SquarePairs
      (ZMod (p*q))) : ℚ) = 4*(p : ℚ)*q-2*((p : ℚ)+q)+1 := by
    exact_mod_cast hC
  rw [hCQ] at h
  push_cast at h
  linarith

theorem semiprime_primeArm_projects (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (hp2 : (2 : ZMod p) ≠ 0)
    (hq2 : (2 : ZMod q) ≠ 0) :
    primeArmOperator (sourceGram (ZMod (p*q))) (sourceZero (ZMod (p*q))) =
      Matrix.diagonal (fun r => if (fibreCount (ZMod (p*q)) r : ℚ)=2 then 1 else 0) := by
  classical
  have hz : (fibreCount (ZMod (p*q)) 0 : ℚ)=1 := by
    exact_mod_cast semiprime_zero_fibre p q hpq
  have hlive : ∀ r : ZMod (p*q), r ≠ 0 →
      (fibreCount (ZMod (p*q)) r : ℚ)=0 ∨
      (fibreCount (ZMod (p*q)) r : ℚ)=2 ∨
      (fibreCount (ZMod (p*q)) r : ℚ)=4 := by
    intro r hr
    rcases semiprime_nonzero_fibre p q hpq hp2 hq2 r hr with h | h | h
    · left; exact_mod_cast h
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
  have h := primeArm_projects (fun r : ZMod (p*q) => (fibreCount _ r : ℚ)) 0 hz hlive
  ext i j
  simpa only [sourceGram, sourceZero, Matrix.diagonal_apply] using
    congrArg (fun M : Matrix (ZMod (p*q)) (ZMod (p*q)) ℚ => M i j) h

/-- An explicit N-only reference evaluator. Its complete finite pair fold is
charged to its budget; it is not the proposed non-enumerative producer. -/
def referenceCollisionCount (N : ℕ+) : ℕ :=
  ((Finset.univ : Finset (ZMod (N : ℕ) × ZMod (N : ℕ))).filter
    (fun xy => xy.1^2=xy.2^2)).card

/-- Computable from the numeral N alone, without supplied factors or spectra. -/
def traceFromN (N : ℕ+) : ℚ :=
  (4*(N : ℚ)-(referenceCollisionCount N : ℚ)-3)/4

theorem referenceCollisionCount_card (N : ℕ+) :
    referenceCollisionCount N =
      Fintype.card (Imscribing.SourceBraidSquareCollision.SquarePairs (ZMod (N : ℕ))) := by
  classical
  simp only [referenceCollisionCount,
    Imscribing.SourceBraidSquareCollision.SquarePairs, Fintype.card_subtype]

theorem reference_pair_extent (N : ℕ+) :
    (Finset.univ : Finset (ZMod (N : ℕ) × ZMod (N : ℕ))).card =
      (N : ℕ)*(N : ℕ) := by
  simp [ZMod.card]

theorem traceFromN_eq_source_trace (N : ℕ+) :
    traceFromN N = Matrix.trace (primeArmOperator (sourceGram (ZMod (N : ℕ)))
      (sourceZero (ZMod (N : ℕ)))) := by
  have h := trace_primeArm (sourceGram (ZMod (N : ℕ))) (sourceZero (ZMod (N : ℕ)))
  rw [sourceGram_trace, sourceGram_trace_square, sourceZero_trace, ZMod.card] at h
  unfold traceFromN
  rw [referenceCollisionCount_card]
  linarith

#print axioms semiprime_nonzero_fibre
#print axioms primeArm_projects
#print axioms semiprime_primeArm_trace
#print axioms semiprime_primeArm_projects
#print axioms traceFromN_eq_source_trace

end Imscribing.SourceBraidPrimeArmProjection
