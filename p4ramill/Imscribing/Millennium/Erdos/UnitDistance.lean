-- Imscribing/Millennium/Erdos/UnitDistance.lean
-- Unit distance problem
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §9  UNIT DISTANCE PROBLEM — f_d(n) across dimensions
-- ============================================================

/-!
**Erdős Unit Distance Problem:** Let f_d(n) be the maximum number
of unit-distance pairs among n points in ℝ^d. Determine the
asymptotic growth of f_d(n) for each dimension d.

**mOMonadOS Agent FSPLIT Decomposition (Cycle 7):**

  Branch 1 — Dimension_2 (structural): Planar unit distances.
    Upper bound O(n^{4/3}) via Spencer-Szemerédi-Trotter incidence
    geometry. Lower bound n^{1+c/log log n} via √n×√n grid.
    The gap between n^{1+o(1)} and n^{4/3} is the central
    transcendental friction.

  Branch 2 — Dimension_3 (statistical): Spatial unit distances.
    Lower bound n^{4/3} log log n (3D grid). Upper bound
    O(n^{3/2} β(n)) via Clarkson et al. (1990), where β(n) is
    an inverse-Ackermann factor from Voronoi complexity.

  Branch 3 — Dimension_d≥4 (obstructional): High dimensions.
    Lenz construction: place points on p=⌊d/2⌋ orthogonal 2-circles.
    Erdős-Stone gives the Turán bound: f_d(n) ≈ T(n,p) + O(n).
    For even d≥4: f_d(n) = ⌊n²/4⌋ + n (Brass, 1997, for d=4).
    For odd d≥5: add n^{4/3} correction (Erdős-Pach).

**Phase transition at d=4:** d≤3 is incidence-geometric (subquadratic);
d≥4 is graph-theoretic (quadratic). The Lenz construction exploits
orthogonal circles to create K_{p,p}-free unit distance graphs.

**Structural Imscription — unit_distance_problem:**
  D=ash (finite point sets → simplicial incidence geometry)
  T=mime (crossing: Lenz circles intersect orthogonally at d≥4)
  R=ear (bipartite ↔ unit distance duality)
  P=out (subquadratic vs. quadratic partition)
  F=peep (combinatorial precision via crossing number / regularity)
  K=egg (asymptotic convergence with n)
  G=thigh (intermediate: sphere incidences at d=3)
  Γ=measure (sequential n→∞)
  φ̂=roar (complex-axis: Lenz circles are 1-dim complex manifolds)
  H=kick (weak chiral: distance is symmetric but graph edges are
    directed by construction order)
  Σ=hung (1:1: one point set → one f_d(n) supremum)
  Ω=oak (ℤ₂ parity: even/odd dimension determines the Turán floor)
-/

/-! ### The Lenz construction at d = 4, machine-checked

Branch 3 above is the branch that is actually settled, and its content is a
coordinate computation: two circles of radius `1/√2` in orthogonal planes of
`ℝ⁴`, every point of one at distance exactly `1` from every point of the other.
Everything quadratic about `f_d(n)` for `d ≥ 4` comes from that one fact, and
it was prose.

A circle point is carried here by a unit vector of `ℝ²` rather than an angle:
the same circle, but distinctness of points is then read straight off the
coordinates instead of needing injectivity of `θ ↦ (cos θ, sin θ)` on a period.
-/

namespace Lenz

open Finset

/-- A point of the first Lenz circle: radius `1/√2` in the `x₀x₁`-plane. -/
noncomputable def circA (v : ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[v.1 / Real.sqrt 2, v.2 / Real.sqrt 2, 0, 0]

/-- A point of the second Lenz circle: radius `1/√2` in the orthogonal
`x₂x₃`-plane. -/
noncomputable def circB (w : ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[0, 0, w.1 / Real.sqrt 2, w.2 / Real.sqrt 2]

/-- The Lenz identity: the two circles are at constant distance `1`. Each
circle contributes `1/2` to the squared distance because the planes are
orthogonal, and `1/2 + 1/2 = 1` — no condition beyond both vectors being
unit vectors. -/
theorem dist_circA_circB (v w : ℝ × ℝ)
    (hv : v.1 ^ 2 + v.2 ^ 2 = 1) (hw : w.1 ^ 2 + w.2 ^ 2 = 1) :
    dist (circA v) (circB w) = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  rw [EuclideanSpace.dist_eq]
  simp only [circA, circB, Fin.sum_univ_four, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Real.dist_eq]
  have : |v.1 / Real.sqrt 2 - 0| ^ 2 + |v.2 / Real.sqrt 2 - 0| ^ 2
       + |(0:ℝ) - w.1 / Real.sqrt 2| ^ 2 + |(0:ℝ) - w.2 / Real.sqrt 2| ^ 2 = 1 := by
    simp only [sub_zero, zero_sub, abs_neg, sq_abs, div_pow]
    field_simp [h2]
    nlinarith [hv, hw]
  rw [this, Real.sqrt_one]


/-- Distinct unit vectors give distinct circle points: the coordinates are the
data, so injectivity is division by `√2 ≠ 0`. -/
theorem circA_injective : Function.Injective circA := by
  intro v v' h
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have h0 : v.1 / Real.sqrt 2 = v'.1 / Real.sqrt 2 := by
    simpa [circA] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 0) h
  have h1 : v.2 / Real.sqrt 2 = v'.2 / Real.sqrt 2 := by
    simpa [circA] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 1) h
  exact Prod.ext (by field_simp at h0; exact h0) (by field_simp at h1; exact h1)

theorem circB_injective : Function.Injective circB := by
  intro w w' h
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have h0 : w.1 / Real.sqrt 2 = w'.1 / Real.sqrt 2 := by
    simpa [circB] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 2) h
  have h1 : w.2 / Real.sqrt 2 = w'.2 / Real.sqrt 2 := by
    simpa [circB] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 3) h
  exact Prod.ext (by field_simp at h0; exact h0) (by field_simp at h1; exact h1)

/-- The two circles are disjoint: a point of one has its `x₀x₁`-part on a
circle of radius `1/√2` and the other has it at the origin. -/
theorem circA_ne_circB {v w : ℝ × ℝ} (hv : v.1 ^ 2 + v.2 ^ 2 = 1) :
    circA v ≠ circB w := by
  intro h
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : v.1 / Real.sqrt 2 = 0 := by
    simpa [circA, circB] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 0) h
  have h1 : v.2 / Real.sqrt 2 = 0 := by
    simpa [circA, circB] using congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 1) h
  rw [div_eq_zero_iff] at h0 h1
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rw [h0, h1] at hv; norm_num at hv
    · exact hne h1
  · exact hne h0


open scoped Classical in
/-- The unit-distance pairs of a finite point set, as ordered pairs. -/
noncomputable def unitPairs (P : Finset (EuclideanSpace ℝ (Fin 4))) :
    Finset (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  (P ×ˢ P).filter (fun q => dist q.1 q.2 = 1)

/-- **The quadratic lower bound.** Splitting the points between the two circles
makes every cross pair a unit distance: the unit-distance graph contains the
complete bipartite graph on the two circles. -/
theorem lenz_pairs_lower (S T : Finset (ℝ × ℝ))
    (hS : ∀ v ∈ S, v.1 ^ 2 + v.2 ^ 2 = 1) (hT : ∀ w ∈ T, w.1 ^ 2 + w.2 ^ 2 = 1) :
    S.card * T.card ≤ (unitPairs (S.image circA ∪ T.image circB)).card := by
  classical
  have hsub : (S.image circA) ×ˢ (T.image circB)
      ⊆ unitPairs (S.image circA ∪ T.image circB) := by
    rintro ⟨q1, q2⟩ hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    simp only at hq1 hq2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq1
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hq2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)
    · exact dist_circA_circB v w (hS v hv) (hT w hw)
  calc S.card * T.card
      = ((S.image circA) ×ˢ (T.image circB)).card := by
        rw [Finset.card_product, Finset.card_image_of_injective _ circA_injective,
          Finset.card_image_of_injective _ circB_injective]
    _ ≤ _ := Finset.card_le_card hsub

/-- The two circles contribute disjoint point sets, so the construction really
has `|S| + |T|` points. -/
theorem lenz_card (S T : Finset (ℝ × ℝ))
    (hS : ∀ v ∈ S, v.1 ^ 2 + v.2 ^ 2 = 1) :
    (S.image circA ∪ T.image circB).card = S.card + T.card := by
  classical
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ circA_injective,
    Finset.card_image_of_injective _ circB_injective]
  refine Finset.disjoint_left.2 ?_
  rintro x hx hx'
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨w, _, hw⟩ := Finset.mem_image.1 hx'
  exact circA_ne_circB (hS v hv) hw.symm

/-! ### Enough circle points to run the construction

The rational parametrization of the circle, used only because it has a visible
left inverse — `t ↦ (1-t²)/(1+t²), 2t/(1+t²)` is recovered by `y/(1+x)` — so
distinctness of parameters gives distinctness of points with no trigonometry.
-/

/-- The rational parametrization of the unit circle. -/
noncomputable def param (t : ℝ) : ℝ × ℝ :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

theorem param_unit (t : ℝ) : (param t).1 ^ 2 + (param t).2 ^ 2 = 1 := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  simp only [param]
  field_simp
  ring

theorem param_left_inv (t : ℝ) : (param t).2 / (1 + (param t).1) = t := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h2 : 1 + (1 - t ^ 2) / (1 + t ^ 2) = 2 / (1 + t ^ 2) := by field_simp; ring
  simp only [param, h2]
  field_simp

theorem param_injective : Function.Injective param := by
  intro a b hab
  have := param_left_inv a
  rw [hab, param_left_inv b] at this
  exact this.symm

/-- `n/2 · (n+1)/2` is `⌊n²/4⌋`, the Turán count the construction realises. -/
theorem half_mul_half (n : ℕ) : n / 2 * ((n + 1) / 2) = n ^ 2 / 4 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · rw [show (k + k) ^ 2 = 4 * (k * k) by ring, Nat.mul_div_cancel_left _ (by norm_num),
      show (k + k) / 2 = k by omega, show (k + k + 1) / 2 = k by omega]
  · rw [show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring,
      show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (4 * (k * k + k) + 1) / 4 = k * k + k by omega]
    ring

/-- **The Lenz bound, assembled.** For every `n` there are `n` points of `ℝ⁴`
spanning at least `⌊n²/4⌋` unit distances — the quadratic lower bound that makes
`d ≥ 4` a Turán problem rather than an incidence problem. -/
theorem lenz_lower_bound (n : ℕ) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 4)),
      P.card = n ∧ n ^ 2 / 4 ≤ (unitPairs P).card := by
  classical
  set S : Finset (ℝ × ℝ) := (Finset.range (n / 2)).image (fun i : ℕ => param (i : ℝ)) with hSdef
  set T : Finset (ℝ × ℝ) := (Finset.range ((n + 1) / 2)).image (fun i : ℕ => param (i : ℝ)) with hTdef
  have hinj : Function.Injective (fun i : ℕ => param (i : ℝ)) :=
    param_injective.comp (fun a b h => Nat.cast_injective h)
  have hScard : S.card = n / 2 := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hTcard : T.card = (n + 1) / 2 := by
    rw [hTdef, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hSu : ∀ v ∈ S, v.1 ^ 2 + v.2 ^ 2 = 1 := by
    intro v hv; obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv; exact param_unit _
  have hTu : ∀ w ∈ T, w.1 ^ 2 + w.2 ^ 2 = 1 := by
    intro w hw; obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hw; exact param_unit _
  refine ⟨S.image circA ∪ T.image circB, ?_, ?_⟩
  · rw [lenz_card S T hSu, hScard, hTcard]; omega
  · rw [← half_mul_half, ← hScard, ← hTcard]
    exact lenz_pairs_lower S T hSu hTu

#print axioms dist_circA_circB
#print axioms lenz_lower_bound

end Lenz

/--
The unit distance problem as an Imscription.
Tier: O₂ — roar+oak at thigh with mime topology gives O₂.
-/
def unit_distance_problem : Imscription :=
  { dim  := Dimensionality.ash
    top  := Topology.mime
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.kick
    stoi := Stoichiometry.hung
    prot := Protection.oak }

theorem unit_distance_problem_tier : imscriptionTier unit_distance_problem = .O₂ := by
  unfold unit_distance_problem; native_decide

/-!
**Why Ω=oak (ℤ₂)?** The dimension parity determines the asymptotic:
even d≥4 uses Turán with floor p=d/2; odd d≥5 adds n^{4/3} lower-order
term. This ℤ₂ parity protection is structural — the Lenz construction
fundamentally differs for even vs. odd dimension.

**mOMonadOS Agent Verdict:** Belnap **B** — Both True (d≥4 is
essentially resolved via Turán theory) and Neither (d=2,3 have
polynomial gaps between lower/upper bounds: n^{1+o(1)} vs n^{4/3}
for d=2; n^{4/3} vs n^{3/2} for d=3).

**Known Results:**
  ✓ Lenz: two orthogonal circles of radius 1/√2 in ℝ⁴ are at constant
    distance 1 — `Lenz.dist_circA_circB`, machine-checked
  ✓ Lenz bound: f₄(n) ≥ ⌊n²/4⌋ for every n — `Lenz.lenz_lower_bound`,
    machine-checked; the matching upper bound and the +n in Brass's exact
    value are cited, not proved here
  ✓ Spencer-Szemerédi-Trotter (1984): d=2 upper bound O(n^{4/3})
  ✓ Clarkson et al. (1990): d=3 bound O(n^{3/2} β(n))
  ✓ Brass (1997): d=4 exact: f_4(n) = ⌊n²/4⌋ + n
  ✓ Erdős-Pach: odd d≥5 correction n^{4/3}
  ✗ Optimal constant for d=2,3
  ✗ Is f_2(n) = n^{1+c/log log n} the true order? (Erdős $500)

**Barrier:** The d=2 gap requires improving Szemerédi-Trotter for
unit distances, which has resisted improvement for 40 years.
Diffs to kernel: D(ash→if'), T(mime→are), Ω(oak→zoo).
-/

end Millennium.ErdosProblems
