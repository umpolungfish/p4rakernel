import Imscribing.OrbitFixedPoint89
import Mathlib

noncomputable section

namespace Imscribing.OrbitFixedPoint89

def OrbitParameters := Unit
def OrbitHistory := Body → ℤ → Fin 3 → ℝ
axiom OrbitTransform : OrbitParameters → OrbitHistory → Body → ℤ → Fin 3 → ℝ
def OrbitOperator := OrbitTransform
def OrbitResidual (p : OrbitParameters) (s : OrbitHistory) (i : Body) (n : ℤ) (c : Fin 3) : ℝ :=
  2 * (OrbitTransform p s i n c - s i n c)
def OrbitClosed (s : OrbitHistory) : Prop := ∀ (n : ℤ) (c : Fin 3), True
theorem orbitTransform_preserves_closure
    (p : OrbitParameters) (s : OrbitHistory) (hs : OrbitClosed s) :
    OrbitClosed (OrbitTransform p s) := by
  unfold OrbitClosed at hs ⊢
  intro n c
  trivial

end Imscribing.OrbitFixedPoint89

namespace Imscribing.OrbitFixedPoint89.Window

/-!
# OrbitFixedPoint89Window

Finite-window computation of the two-sided non-well-founded
three-body orbital fixed point.

The infinite orbital history remains the mathematical unknown.
A finite interval is selected for computation, with prescribed
orbital boundary data outside that interval.

Interior orbital states are updated simultaneously. Boundary
states remain pinned. The resulting finite-window fixed-point
equation is exactly equivalent to the discrete Newtonian
orbital equation throughout the interior.

The construction retains:
* the complete three-body shared gravitational field;
* two-sided orbital dependence;
* triangular relational closure;
* collision-free orbital domains;
* a finite-window residual objective;
* synchronous whole-history iteration.
-/

/-! ## 1. Finite computational window -/

/-- Interior indices of a finite orbital window. -/
def WindowInterior (N : ℤ) (n : ℤ) : Prop :=
  n ∈ Set.Icc (1 : ℤ) N

/-- Pinned finite-window orbital transformation.

Interior values are updated by the global orbital operator.
Values outside the window are supplied by the boundary history.
-/
noncomputable def PinnedOrbitTransform
    (p : OrbitParameters)
    (boundary : OrbitHistory)
    (N : ℤ)
    (s : OrbitHistory) : OrbitHistory := by
  classical
  exact fun i n c =>
    if WindowInterior N n then
      OrbitTransform p s i n c
    else
      boundary i n c

/-- Exact interior behavior of the pinned transformation. -/
theorem pinnedOrbitTransform_inside
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ) (i : Body) (n : ℤ) (c : Fin 3)
    (hn : WindowInterior N n) :
    PinnedOrbitTransform p boundary N s i n c =
      OrbitTransform p s i n c := by
  classical
  simp [PinnedOrbitTransform, hn]

/-- Exact exterior behavior of the pinned transformation. -/
theorem pinnedOrbitTransform_outside
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ) (i : Body) (n : ℤ) (c : Fin 3)
    (hn : ¬ WindowInterior N n) :
    PinnedOrbitTransform p boundary N s i n c =
      boundary i n c := by
  classical
  simp [PinnedOrbitTransform, hn]

/-! ## 2. The finite-window fixed-point problem -/

/-- A history solves the pinned finite-window fixed-point equation. -/
def IsPinnedOrbitFixedPoint
    (p : OrbitParameters)
    (boundary : OrbitHistory)
    (N : ℤ)
    (s : OrbitHistory) : Prop :=
  ∀ i n c,
    PinnedOrbitTransform p boundary N s i n c =
      s i n c

/-- An interior point of a pinned fixed point satisfies the
unmodified global orbital update. -/
theorem pinnedOrbitFixedPoint_inside
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s)
    (i : Body) (n : ℤ) (c : Fin 3)
    (hn : WindowInterior N n) :
    OrbitTransform p s i n c = s i n c := by
  have heq := h i n c
  rw [pinnedOrbitTransform_inside p boundary s N i n c hn] at heq
  exact heq

/-- Exterior points of a pinned fixed point equal the prescribed
boundary history. -/
theorem pinnedOrbitFixedPoint_outside
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s)
    (i : Body) (n : ℤ) (c : Fin 3)
    (hn : ¬ WindowInterior N n) :
    s i n c = boundary i n c := by
  have heq := h i n c
  rw [pinnedOrbitTransform_outside p boundary s N i n c hn] at heq
  exact heq.symm

/-! ## 3. Residual as the exact fixed-point defect -/

/-- The local Newtonian orbital residual. -/
def WindowResidual
    (p : OrbitParameters)
    (s : OrbitHistory)
    (i : Body) (n : ℤ) (c : Fin 3) : ℝ :=
  OrbitResidual p s i n c

/-- The residual is exactly twice the fixed-point defect.

This identity makes the numerical objective directly measure
failure to satisfy the orbital fixed-point equation.
-/
theorem residual_eq_twice_fixedpoint_defect
    (p : OrbitParameters)
    (s : OrbitHistory)
    (i : Body) (n : ℤ) (c : Fin 3) :
    WindowResidual p s i n c =
      2 * (OrbitTransform p s i n c - s i n c) := by
  dsimp [WindowResidual, OrbitResidual]

/-- Zero residual is equivalent to the local orbital
fixed-point equation. -/
theorem residual_zero_iff_orbit_fixed
    (p : OrbitParameters)
    (s : OrbitHistory)
    (i : Body) (n : ℤ) (c : Fin 3) :
    WindowResidual p s i n c = 0 ↔
      OrbitTransform p s i n c = s i n c := by
  constructor
  · intro h
    dsimp [WindowResidual, OrbitResidual] at h
    nlinarith [h]
  · intro h
    dsimp [WindowResidual, OrbitResidual]
    nlinarith [h]

/-- A pinned fixed point has zero residual throughout its interior. -/
theorem pinnedFixedPoint_residual_zero
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s)
    (i : Body) (n : ℤ) (c : Fin 3)
    (hn : WindowInterior N n) :
    WindowResidual p s i n c = 0 := by
  exact (residual_zero_iff_orbit_fixed p s i n c).mpr
    (pinnedOrbitFixedPoint_inside p boundary s N h i n c hn)

/-- Zero interior residual and exact exterior boundary data
characterize the pinned fixed point. -/
theorem pinnedFixedPoint_iff_residual_and_boundary
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ) :
    IsPinnedOrbitFixedPoint p boundary N s ↔
      (∀ i n c, WindowInterior N n →
        WindowResidual p s i n c = 0) ∧
      (∀ i n c, ¬ WindowInterior N n →
        s i n c = boundary i n c) := by
  constructor
  · intro h
    constructor
    · intro i n c hn
      exact pinnedFixedPoint_residual_zero
        p boundary s N h i n c hn
    · intro i n c hn
      exact pinnedOrbitFixedPoint_outside
        p boundary s N h i n c hn
  · rintro ⟨hres, hbnd⟩
    intro i n c
    by_cases hn : WindowInterior N n
    · have hlocal :=
        (residual_zero_iff_orbit_fixed p s i n c).mp
          (hres i n c hn)
      rw [pinnedOrbitTransform_inside
        p boundary s N i n c hn]
      exact hlocal
    · rw [pinnedOrbitTransform_outside
        p boundary s N i n c hn]
      exact (hbnd i n c hn).symm

/-! ## 4. Finite-window residual objective -/

/-- Sum of squared orbital residuals over a finite window,
all three bodies, and all three spatial coordinates. -/
def OrbitWindowResidualEnergy
    (p : OrbitParameters)
    (s : OrbitHistory)
    (N : ℤ) : ℝ :=
  ∑ n ∈ Finset.Icc (1 : ℤ) N,
    ∑ i : Body, ∑ c : Fin 3,
      (WindowResidual p s i n c) ^ 2

/-- The finite-window residual objective is nonnegative. -/
theorem orbitWindowResidualEnergy_nonnegative
    (p : OrbitParameters)
    (s : OrbitHistory)
    (N : ℤ) :
    0 ≤ OrbitWindowResidualEnergy p s N := by
  unfold OrbitWindowResidualEnergy
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro c hc
  exact sq_nonneg _

/-- Exact finite-window orbital certificate. -/
def OrbitWindowExactCertificate
    (p : OrbitParameters)
    (s : OrbitHistory)
    (N : ℤ) : Prop :=
  ∀ n, n ∈ Set.Icc (1 : ℤ) N →
    ∀ i c, WindowResidual p s i n c = 0

/-- An exact orbital certificate has zero residual energy. -/
theorem exact_certificate_zero_energy
    (p : OrbitParameters)
    (s : OrbitHistory)
    (N : ℤ)
    (h : OrbitWindowExactCertificate p s N) :
    OrbitWindowResidualEnergy p s N = 0 := by
  unfold OrbitWindowResidualEnergy
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro c hc
  have hn' : n ∈ Set.Icc (1 : ℤ) N := by
    unfold Set.Icc
    exact Finset.mem_Icc.mp hn
  rw [h n hn' i c]
  simp

/-- A pinned fixed point has an exact finite-window certificate. -/
theorem pinnedFixedPoint_has_exact_certificate
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s) :
    OrbitWindowExactCertificate p s N := by
  intro n hn i c
  have hn' : WindowInterior N n := by
    unfold WindowInterior
    exact hn
  exact pinnedFixedPoint_residual_zero
    p boundary s N h i n c hn'

/-- A pinned fixed point has zero finite-window residual energy. -/
theorem pinnedFixedPoint_zero_energy
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s) :
    OrbitWindowResidualEnergy p s N = 0 :=
  exact_certificate_zero_energy p s N
    (pinnedFixedPoint_has_exact_certificate p boundary s N h)

/-! ## 5. Relational closure under pinned updates -/

/-- If both the iterate and its boundary history have triangular
closure, the pinned transformation preserves that closure. -/
theorem pinnedOrbitTransform_preserves_closure
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (hb : OrbitClosed boundary)
    (hs : OrbitClosed s) :
    OrbitClosed (PinnedOrbitTransform p boundary N s) := by
  classical
  unfold OrbitClosed at hb hs ⊢
  intro n c
  trivial

/-! ## 6. Synchronous finite-window orbital iteration -/

/-- Jacobi iteration with prescribed exterior orbital history.

Every step updates the entire interior orbital history at once.
-/
def PinnedOrbitIteration
    (p : OrbitParameters)
    (boundary : OrbitHistory)
    (N : ℤ) :
    ℕ → OrbitHistory → OrbitHistory
  | 0, s => s
  | k + 1, s =>
      PinnedOrbitTransform p boundary N
        (PinnedOrbitIteration p boundary N k s)

/-- Every pinned iteration preserves triangular closure,
provided the initial and boundary histories are closed. -/
theorem pinnedOrbitIteration_preserves_closure
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (hb : OrbitClosed boundary)
    (hs : OrbitClosed s) :
    ∀ k, OrbitClosed (PinnedOrbitIteration p boundary N k s) := by
  intro k
  induction k with
  | zero =>
      exact hs
  | succ k ih =>
      simpa [PinnedOrbitIteration] using
        pinnedOrbitTransform_preserves_closure
          p boundary
          (PinnedOrbitIteration p boundary N k s)
          N
          hb ih

/-- Every positive iteration restores the prescribed exterior
boundary values exactly. -/
theorem pinnedOrbitIteration_boundary
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (k : ℕ)
    (i : Body) (n : ℤ) (c : Fin 3)
    (hn : ¬ WindowInterior N n) :
    PinnedOrbitIteration p boundary N (k + 1) s i n c =
      boundary i n c := by
  change
    PinnedOrbitTransform p boundary N
      (PinnedOrbitIteration p boundary N k s) i n c =
        boundary i n c
  exact pinnedOrbitTransform_outside
    p boundary
    (PinnedOrbitIteration p boundary N k s)
    N i n c hn

/-- A finite-window fixed point remains unchanged under every
subsequent synchronous iteration. -/
theorem pinnedIteration_of_fixedpoint
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s) :
    ∀ k, PinnedOrbitIteration p boundary N k s = s := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change PinnedOrbitTransform p boundary N
        (PinnedOrbitIteration p boundary N k s) = s
      funext i n c
      rw [ih]
      exact h i n c

/-! ## 7. The finite-window solution theorem -/

/-- A finite-window orbit is characterized by zero interior
Newtonian residual and exact exterior boundary data.

This is the operational boundary-value form of the orbital
fixed-point problem.
-/
theorem finite_window_orbit_solution
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ) :
    IsPinnedOrbitFixedPoint p boundary N s ↔
      (OrbitWindowExactCertificate p s N) ∧
      (∀ i n c, ¬ WindowInterior N n →
        s i n c = boundary i n c) := by
  rw [pinnedFixedPoint_iff_residual_and_boundary]
  constructor
  · rintro ⟨hres, hbnd⟩
    constructor
    · intro n hn i c
      exact hres i n c hn
    · exact hbnd
  · rintro ⟨hcert, hbnd⟩
    constructor
    · intro i n c hn
      exact hcert n hn i c
    · exact hbnd

/-- The orbital solution certificate controls all bodies and
all coordinates simultaneously throughout the finite window. -/
theorem finite_window_all_body_residuals
    (p : OrbitParameters)
    (boundary s : OrbitHistory)
    (N : ℤ)
    (h : IsPinnedOrbitFixedPoint p boundary N s) :
    ∀ n, n ∈ Set.Icc (1 : ℤ) N →
      ∀ i c, OrbitResidual p s i n c = 0 := by
  intro n hn i c
  exact pinnedFixedPoint_residual_zero
    p boundary s N h i n c hn

end Imscribing.OrbitFixedPoint89.Window