import Imscribing.Millennium.Erdos.Problems.Problem0028
import Imscribing.PrimeWhorlTheory
import Imscribing.Millennium.ZetaSICDualFrame
import Imscribing.Classical.WindowedBound
import Imscribing.Classical.ErdosTuranParitySIC
import Imscribing.Millennium.HornTorusGeometry

/-!
# Erdős #28 through a PrimeWhorl phase coordinate

For a fixed sum `a + b = n`, the rational phase `(a+1)/(b+1)` is a faithful
coordinate for the ordered representation `(a,b)`. The mirrored PrimeWhorl
crossing reads its defect as `1 - phase`; the phase embeds on the horn torus's
equatorial circle with a coordinate-ratio inverse; ZetaSIC's exact dual recovers
the finite phase payload. Thus the representation multiplicity survives all
three transforms exactly. This is a representation bridge, not yet the missing
argument that the fiber multiplicities are unbounded.
-/

namespace Imscribing.Millennium.Erdos.Problem0028HornWhorlSIC

open Finset
open Imscribing.PrimeWhorl
open Imscribing.PrimeWhorl.Burau
open Imscribing.PrimeWhorl.Theory
open Imscribing.Millennium.ZetaSICDualFrame
open Imscribing.Classical
open Imscribing.Classical.ErdosTuranParitySIC
open Imscribing.HornTorus

/-- Positive rational phase attached to an ordered pair. -/
def representationPhase (a b : ℕ) : ℚ :=
  ((a : ℚ) + 1) / ((b : ℚ) + 1)

/-- The ratio is a certified unit, so it can act in the PrimeWhorl Burau braid. -/
def representationUnitPhase (a b : ℕ) : UnitPhase ℚ where
  t := representationPhase a b
  tinv := representationPhase b a
  mul_inv := by
    have ha : (a : ℚ) + 1 ≠ 0 := by positivity
    have hb : (b : ℚ) + 1 ≠ 0 := by positivity
    simp only [representationPhase]
    field_simp

/-- The PrimeWhorl mirrored crossing reads the pair's phase as a cross-frame
defect. -/
theorem representation_phase_whorl_defect (a b : ℕ) :
    (mirroredBraid (representationUnitPhase a b)).1.x0 -
      (mirroredBraid (representationUnitPhase a b)).2.x0 =
        1 - representationPhase a b := by
  exact mirrored_defect (representationUnitPhase a b)

/-- On a fixed sum fiber, the phase distinguishes ordered representations. -/
theorem representationPhase_injective_on_sum {n : ℕ}
    {a b c d : ℕ} (hab : a + b = n) (hcd : c + d = n)
    (hphase : representationPhase a b = representationPhase c d) :
    (a, b) = (c, d) := by
  have ha : (a : ℚ) + 1 ≠ 0 := by positivity
  have hb : (b : ℚ) + 1 ≠ 0 := by positivity
  have hc : (c : ℚ) + 1 ≠ 0 := by positivity
  have hd : (d : ℚ) + 1 ≠ 0 := by positivity
  have hcross : ((a : ℚ) + 1) * ((d : ℚ) + 1) =
      ((c : ℚ) + 1) * ((b : ℚ) + 1) := by
    dsimp [representationPhase] at hphase
    have := congrArg (fun x : ℚ => x * (((b : ℚ) + 1) * ((d : ℚ) + 1))) hphase
    field_simp [hb, hd] at this
    nlinarith
  have hab' : (a : ℚ) + b = n := by exact_mod_cast hab
  have hcd' : (c : ℚ) + d = n := by exact_mod_cast hcd
  have hac : (a : ℚ) = c := by nlinarith [hcross, hab', hcd']
  have hacNat : a = c := by exact_mod_cast hac
  have hbd : b = d := by omega
  exact Prod.ext hacNat hbd

/-- The finite-frame representation set used by `r`. -/
noncomputable def representationFrame (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((A_n A n) ×ˢ (A_n A n)).filter (fun p => p.1 + p.2 = n)

/-- Reading the whole fixed-sum fiber into phase coordinates is injective. -/
theorem representation_phase_readout_injective (A : Set ℕ) (n : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => representationPhase p.1 p.2)
      (representationFrame A n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hpFin : p ∈ representationFrame A n := Finset.mem_coe.mp hp
  have hqFin : q ∈ representationFrame A n := Finset.mem_coe.mp hq
  have hp' := (Finset.mem_filter.mp hpFin).2
  have hq' := (Finset.mem_filter.mp hqFin).2
  exact representationPhase_injective_on_sum hp' hq' heq

/-- Embed the PrimeWhorl phase of an ordered representation on the equatorial
circle of the radius-two horn torus. The arctangent keeps the phase in the
single-valued angular chart. -/
noncomputable def representationHornPoint (a b : ℕ) : Point :=
  horn 2 0 (Real.arctan (representationPhase a b : ℝ))

/-- The equatorial coordinate ratio recovers the rational representation phase
exactly. This makes the horn-torus passage injective rather than a lossy visual
encoding. -/
theorem representation_horn_readout (a b : ℕ) :
    (representationHornPoint a b).2.1 / (representationHornPoint a b).1 =
      (representationPhase a b : ℝ) := by
  simp [representationHornPoint, horn, Real.cos_arctan, Real.sin_arctan]
  have hden : 0 < Real.sqrt (1 + (representationPhase a b : ℝ) ^ 2) := by
    apply Real.sqrt_pos.2
    positivity
  field_simp
  <;> ring

/-- On a fixed sum fiber the horn-torus coordinates distinguish every ordered
representation, by reading the phase back from the two equatorial coordinates. -/
theorem representation_horn_injective_on_sum {n : ℕ}
    {a b c d : ℕ} (hab : a + b = n) (hcd : c + d = n)
    (hpoint : representationHornPoint a b = representationHornPoint c d) :
    (a, b) = (c, d) := by
  have hread := congrArg (fun p : Point => p.2.1 / p.1) hpoint
  change (representationHornPoint a b).2.1 / (representationHornPoint a b).1 =
    (representationHornPoint c d).2.1 / (representationHornPoint c d).1 at hread
  rw [representation_horn_readout, representation_horn_readout] at hread
  exact representationPhase_injective_on_sum hab hcd (by exact_mod_cast hread)

/-- The horn-torus readout has exactly the same finite fiber cardinality as the
ordered representation function. -/
theorem representation_horn_card (A : Set ℕ) (n : ℕ) :
    ((representationFrame A n).image (fun p => representationHornPoint p.1 p.2)).card =
      r A n := by
  calc
    ((representationFrame A n).image (fun p => representationHornPoint p.1 p.2)).card =
        (representationFrame A n).card :=
      Finset.card_image_iff.mpr (by
        intro p hp q hq heq
        have hpFin := Finset.mem_coe.mp hp
        have hqFin := Finset.mem_coe.mp hq
        have hps := (Finset.mem_filter.mp hpFin).2
        have hqs := (Finset.mem_filter.mp hqFin).2
        exact representation_horn_injective_on_sum hps hqs heq)
    _ = r A n := by simp [r, representationFrame, A_n]

/-- The number of distinct PrimeWhorl phase readouts equals `r A n` exactly. -/
theorem representation_phase_card (A : Set ℕ) (n : ℕ) :
    ((representationFrame A n).image (fun p => representationPhase p.1 p.2)).card =
      r A n := by
  calc
    ((representationFrame A n).image (fun p => representationPhase p.1 p.2)).card =
        (representationFrame A n).card :=
      Finset.card_image_iff.mpr (representation_phase_readout_injective A n)
    _ = r A n := by
      simp [r, representationFrame, A_n]

/-- Odd coefficients locate the doubled source elements, and ZetaSIC
reconstructs this finite parity coefficient vector exactly. The separate
PrimeWhorl phase readout above preserves every ordered pair in a sum fiber. -/
theorem finite_parity_signal_zeta_reconstruction
    (B : Finset ℕ) (N : ℕ) (hB : ∀ a ∈ B, a ≤ N) :
    (oddRepresentationSums B N).card = B.card ∧
    (sicDualGeneral (paritySICDimension N)).mulVec
      ((sicGramGeneral (paritySICDimension N)).mulVec
        (paritySICPayload B N)) = paritySICPayload B N := by
  exact ⟨card_odd_representation_sums B N hB,
    zeta_sic_recovers_parity_payload B N⟩

/-- A finite subfamily's ordered representations are contained in the full
    representation fiber. This is the bridge from a global bound on `r A n`
    to the local Sidon windows used by the windowed argument. -/
theorem finite_reps_card_le (A : Set ℕ) (n : ℕ) (B : Finset ℕ)
    (hBA : (↑B : Set ℕ) ⊆ A) :
    (Imscribing.Classical.reps B n).card ≤ r A n := by
  classical
  have hsubset : Imscribing.Classical.reps B n ⊆
      Imscribing.Classical.reps (A_n A n) n := by
    intro p hp
    obtain ⟨ha, hb, hsum⟩ := Imscribing.Classical.mem_reps.mp hp
    have ha' : p.1 ∈ A_n A n := by
      simp only [A_n, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, by omega⟩, hBA (Finset.mem_coe.mpr ha)⟩
    have hb' : p.2 ∈ A_n A n := by
      simp only [A_n, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, by omega⟩, hBA (Finset.mem_coe.mpr hb)⟩
    exact Imscribing.Classical.mem_reps.mpr ⟨ha', hb', hsum⟩
  calc
    (Imscribing.Classical.reps B n).card ≤
        (Imscribing.Classical.reps (A_n A n) n).card := Finset.card_le_card hsubset
    _ = r A n := by simp [r, Imscribing.Classical.reps, A_n]

/-- **A nonnegative asymptotic basis cannot keep `r_A(n) ≤ 2` for every
target.** No positivity hypothesis is needed: the windowed Sidon contradiction
also includes zero in its finite source windows. -/
theorem basis_representation_bound_two_impossible (A : Set ℕ)
    (h_basis : ∃ N₀, ∀ n ≥ N₀, n ∈ sumset A)
    (h_bound : ∀ n : ℕ, r A n ≤ 2) : False := by
  obtain ⟨N₀, hbasis⟩ := h_basis
  apply Imscribing.Classical.no_basis_with_reps_le_two A N₀
  · intro n hn
    rcases hbasis n hn with ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab⟩
  · intro n B hBA
    exact (finite_reps_card_le A n B hBA).trans (h_bound n)

/-- Under a hypothetical global bound of three, every represented target
outside the diagonal set `2A` has exactly two ordered representations. The
bound-three case is not globally Sidon: a diagonal target can have one
diagonal pair and one off-diagonal pair, giving three ordered representations. -/
theorem basis_bound_three_forces_two_off_diagonal (A : Set ℕ)
    (h_bound : ∀ n : ℕ, r A n ≤ 3)
    {n : ℕ} (h_sum : n ∈ sumset A)
    (h_not_double : ¬ ∃ a ∈ A, n = a + a) : r A n = 2 := by
  classical
  let B := A_n A n
  have hB_subset : (↑B : Set ℕ) ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  have hcount : r A n = (reps B n).card := by
    simp [r, B, A_n, reps]
  have hpositive : 0 < r A n :=
    (r_positive_iff A n).2 h_sum
  have hupper : r A n ≤ 3 := h_bound n
  have hfinite_nonempty : (reps B n).Nonempty := by
    apply Finset.card_pos.mp
    rw [← hcount]
    exact hpositive
  have hfinite_not_double : ¬ ∃ a ∈ B, n = a + a := by
    rintro ⟨a, ha, hdouble⟩
    exact h_not_double ⟨a, hB_subset (Finset.mem_coe.mpr ha), hdouble⟩
  have hlower := Imscribing.Classical.two_le_reps_of_nonempty B n
    hfinite_nonempty hfinite_not_double
  have heven := Imscribing.Classical.reps_card_even_off_diagonal B n hfinite_not_double
  rw [hcount] at hupper
  obtain ⟨k, hk⟩ := heven
  omega

/-- The cap-three case has an exact coefficient split: a represented
non-doubled target has coefficient two, while a represented doubled target
has coefficient one or three. The latter alternatives are precisely the two
possible values of a positive odd coefficient below the cap. -/
theorem basis_bound_three_coefficient_split (A : Set ℕ)
    (h_bound : ∀ n : ℕ, r A n ≤ 3)
    {n : ℕ} (h_sum : n ∈ sumset A) :
    (¬ ∃ a ∈ A, n = a + a) ∧ r A n = 2 ∨
      (∃ a ∈ A, n = a + a ∧ (r A n = 1 ∨ r A n = 3)) := by
  classical
  by_cases h_double : ∃ a ∈ A, n = a + a
  · right
    obtain ⟨a, ha, hna⟩ := h_double
    have hcount : r A n = (reps (A_n A n) n).card := by
      simp [r, A_n, reps]
    have hfiniteDouble : ∃ b ∈ A_n A n, n = b + b := by
      refine ⟨a, ?_, hna⟩
      simp [A_n, Finset.mem_filter, Finset.mem_Icc, ha]
      omega
    have hodd : Odd (r A n) := by
      rw [hcount]
      exact (Imscribing.Classical.reps_card_odd_iff (A_n A n) n).2 hfiniteDouble
    have hpositive : 0 < r A n := (r_positive_iff A n).2 h_sum
    obtain ⟨k, hk⟩ := hodd
    refine ⟨a, ha, hna, ?_⟩
    have hupper := h_bound n
    omega
  · left
    exact ⟨h_double, basis_bound_three_forces_two_off_diagonal A h_bound h_sum h_double⟩

/-- A doubled target receives the exceptional coefficient three exactly when
its center lies in a nontrivial three-term arithmetic progression in the
basis. The diagonal contributes `(a,a)`; the other two ordered pairs are the
swap orbit of the progression endpoints. -/
theorem basis_bound_three_doubled_target_iff_progression
    (A : Set ℕ) (h_bound : ∀ n : ℕ, r A n ≤ 3) (a : ℕ) (ha : a ∈ A) :
    r A (a + a) = 3 ↔
      ∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ b + c = a + a := by
  classical
  let B := A_n A (a + a)
  have hB_subset : (↑B : Set ℕ) ⊆ A := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
  have haB : a ∈ B := by
    simp [B, A_n, Finset.mem_filter, Finset.mem_Icc, ha]
  have hcount : r A (a + a) = (reps B (a + a)).card := by
    simp [r, B, A_n, reps]
  have hdiag : (onDiag B (a + a)).card = 1 := by
    have hne : (onDiag B (a + a)).Nonempty :=
      (onDiag_nonempty_iff B (a + a)).2 ⟨a, haB, rfl⟩
    have hpos : 0 < (onDiag B (a + a)).card := Finset.card_pos.mpr hne
    have hle := card_onDiag_le_one B (a + a)
    omega
  constructor
  · intro hthree
    have hoff : (Imscribing.Classical.offDiag B (a + a)).card = 2 := by
      have := card_split B (a + a)
      rw [← hcount, hthree, hdiag] at this
      omega
    have hpos : 0 < (Imscribing.Classical.offDiag B (a + a)).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hp' : p ∈ Imscribing.Classical.offDiag B (a + a) := hp
    simp only [Imscribing.Classical.offDiag, Finset.mem_filter] at hp'
    obtain ⟨hpRep, hpNe⟩ := hp'
    obtain ⟨hbB, hcB, hsum⟩ := Imscribing.Classical.mem_reps.mp hpRep
    refine ⟨p.1, hB_subset (Finset.mem_coe.mpr hbB), p.2,
      hB_subset (Finset.mem_coe.mpr hcB), ?_, hsum⟩
    exact hpNe
  · rintro ⟨b, hb, c, hc, hne, hsum⟩
    have hbB : b ∈ B := by
      simp [B, A_n, Finset.mem_filter, Finset.mem_Icc, hb]
      omega
    have hcB : c ∈ B := by
      simp [B, A_n, Finset.mem_filter, Finset.mem_Icc, hc]
      omega
    have hthree : (reps B (a + a)).card ≥ 3 := by
      let points : Finset (ℕ × ℕ) := {(a, a), (b, c), (c, b)}
      have hsubset : points ⊆ reps B (a + a) := by
        intro p hp
        simp only [points, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with hp | hp | hp
        · subst p
          exact Imscribing.Classical.mem_reps.mpr ⟨haB, haB, rfl⟩
        · rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          exact Imscribing.Classical.mem_reps.mpr ⟨hbB, hcB, hsum⟩
        · rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          exact Imscribing.Classical.mem_reps.mpr ⟨hcB, hbB, by omega⟩
      have hcard : points.card = 3 := by
        simp [points, hne, hne.symm, show (a, a) ≠ (b, c) by
          intro h; have := congrArg Prod.fst h; omega,
          show (a, a) ≠ (c, b) by
          intro h; have := congrArg Prod.fst h; omega]
      exact hcard ▸ Finset.card_le_card hsubset
    have hle : r A (a + a) ≤ 3 := h_bound (a + a)
    rw [hcount]
    omega

/-- Consequently, a hypothetical basis with `r_A(n) ≤ 3` everywhere has
exactly one unordered mixed-parity representation for every sufficiently large
odd target. This isolates the remaining C=3 case to the even targets. -/
theorem odd_represented_targets_have_two_ordered_representations (A : Set ℕ)
    (h_bound : ∀ n : ℕ, r A n ≤ 3)
    {n : ℕ} (hsum : n ∈ sumset A) (hodd : ¬ 2 ∣ n) : r A n = 2 := by
  have hnotDouble : ¬ ∃ a ∈ A, n = a + a := by
    rintro ⟨a, _, h⟩
    exact hodd ⟨a, by omega⟩
  exact basis_bound_three_forces_two_off_diagonal A h_bound hsum hnotDouble

/-- ZetaSIC's general-dimensional exact dual recovers a phase payload without
changing its entries. -/
theorem zeta_sic_recovers_phase_payload (d : ℕ+)
    (phasePayload : Fin ((d : ℕ) ^ 2) → ℂ) :
    (sicDualGeneral d).mulVec ((sicGramGeneral d).mulVec phasePayload) = phasePayload := by
  have hdual := (sic_inverse_general d).1
  rw [Matrix.mulVec_mulVec, hdual, Matrix.one_mulVec]

/-- In particular, the varying-dimensional reconstruction specializes to the
sixteen-coordinate ququart frame. -/
theorem zeta_sic_ququart_payload (phasePayload : Fin 16 → ℂ) :
    ququartDualGram.mulVec (ququartGram.mulVec phasePayload) = phasePayload :=
  ququart_coordinate_reconstruction phasePayload

/-- Give every representation in the finite sum fiber its own SIC coordinate.
The remaining coordinates are zero; the dimension grows with the fiber. -/
noncomputable def representationSICDimension (A : Set ℕ) (n : ℕ) : ℕ+ :=
  ⟨(representationFrame A n).card + 1, Nat.succ_pos _⟩

noncomputable def representationPhasePayload (A : Set ℕ) (n : ℕ) :
    Fin ((representationSICDimension A n : ℕ) ^ 2) → ℂ := by
  classical
  intro j
  by_cases hj : j.val < (representationFrame A n).card
  · let p := (representationFrame A n).equivFin.symm ⟨j.val, hj⟩
    exact ((representationPhase p.val.1 p.val.2 : ℚ) : ℂ)
  · exact 0

/-- The exact ZetaSIC inverse returns the payload indexed by the actual
representations of `n`, so no two representations are identified by readout. -/
theorem zeta_sic_recovers_representation_phase (A : Set ℕ) (n : ℕ) :
    (sicDualGeneral (representationSICDimension A n)).mulVec
      ((sicGramGeneral (representationSICDimension A n)).mulVec
        (representationPhasePayload A n)) = representationPhasePayload A n :=
  zeta_sic_recovers_phase_payload (representationSICDimension A n)
    (representationPhasePayload A n)

/-- The finite representation fiber passes through the PrimeWhorl phase,
the horn-torus embedding, and the ZetaSIC inverse with its multiplicity and
phase payload both preserved. -/
theorem representation_horn_zeta_transport (A : Set ℕ) (n : ℕ) :
    ((representationFrame A n).image
      (fun p => representationHornPoint p.1 p.2)).card = r A n ∧
    (sicDualGeneral (representationSICDimension A n)).mulVec
      ((sicGramGeneral (representationSICDimension A n)).mulVec
        (representationPhasePayload A n)) = representationPhasePayload A n :=
  ⟨representation_horn_card A n, zeta_sic_recovers_representation_phase A n⟩

#print axioms finite_reps_card_le
#print axioms basis_representation_bound_two_impossible
#print axioms basis_bound_three_forces_two_off_diagonal
#print axioms basis_bound_three_doubled_target_iff_progression
#print axioms odd_represented_targets_have_two_ordered_representations

end Imscribing.Millennium.Erdos.Problem0028HornWhorlSIC
