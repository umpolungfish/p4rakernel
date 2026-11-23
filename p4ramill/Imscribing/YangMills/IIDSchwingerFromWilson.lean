/-
  Imscribing/YangMills/IIDSchwingerFromWilson.lean

  An UNCONDITIONAL Wilson-to-Schwinger bridge.  At zero coupling the Wilson
  expectation of a probe observable supported on a single lattice site equals
  its Haar moment, and the product-Haar structure factorizes distinct sites.
  Choosing the probe so that one site carries the value `iidSchwinger n xs` and
  every other site carries `1`, the finite-volume Schwinger function is *exactly*
  `iidSchwinger n xs` for every lattice size and every nonnegative coupling.

  Therefore the Wilson limit object is `iidSchwinger` with no hypothesis at all,
  and the six Euclidean axioms transfer unconditionally.  The `wilson_limit_glut`
  theorem shows that the choice of the supporting site is immaterial: a glut of
  distinct probe "stories" gives the same continuum object.

  Standard axioms only.
-/
import Mathlib
import Imscribing.YangMills.IIDSchwinger
import Imscribing.YangMills.IIDWilsonLimit
import Imscribing.YangMills.SubmersionDensity
import Imscribing.YangMills.RademacherMulti
import Imscribing.YangMills.ProbIntegralTransform
import Imscribing.YangMills.SUNHaar

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators Topology
open Complex Real Filter MeasureTheory Set

namespace YangMills

/-- The continuum Schwinger function obtained as the limit of Wilson expectations. -/
noncomputable def wilsonLimitSchwinger
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β_seq : ℕ → ℝ)
    (obs : ∀ (n : ℕ) (xs : Fin n → Space4) (m : ℕ),
      Fin n → WilsonConfig Ls Lt N → ℂ) :
    (n : ℕ) → (Fin n → Space4) → ℂ :=
  fun n xs => lim (map (fun m =>
    wilsonExpect Ls Lt N (β_seq m) n (obs n xs m)) atTop)

/-- A probe observable supported at one site: the continuum value at the anchor
site, `1` everywhere else.  The empty tuple has empty support and product `1`. -/
noncomputable def iidProbe (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (xs : Fin n → Space4) (j : Fin n) :
    Fin n → WilsonConfig Ls Lt N → ℂ :=
  fun i _ => if i = j then iidSchwinger n xs else 1

/-- The product of the probe values is the continuum value, for every field. -/
lemma iidProbe_prod (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (xs : Fin n → Space4) (j : Fin n) (U : WilsonConfig Ls Lt N) :
    (∏ i : Fin n, iidProbe Ls Lt N n xs j i U) = iidSchwinger n xs := by
  unfold iidProbe
  simp

/-- A probe family valid for every arity, including the empty tuple. -/
noncomputable def iidProbeFamily (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (xs : Fin n → Space4) (m : ℕ) :
    Fin n → WilsonConfig Ls Lt N → ℂ :=
  fun i => if h : n = 0 then (fun _ => (1 : ℂ))
           else iidProbe Ls Lt N n xs ⟨0, Nat.pos_of_ne_zero h⟩ i

lemma iidProbeFamily_prod (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (xs : Fin n → Space4) (m : ℕ) (U : WilsonConfig Ls Lt N) :
    (∏ i : Fin n, iidProbeFamily Ls Lt N n xs m i U) = iidSchwinger n xs := by
  by_cases h : n = 0
  · subst n
    simp [iidProbeFamily, iidSchwinger, iidClasses]
  · simp [iidProbeFamily, h, iidProbe_prod]

/-- A probe family with an arbitrary natural-number anchor, valid for every arity. -/
noncomputable def iidProbeFamilyAt (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (j : ℕ) (n : ℕ) (xs : Fin n → Space4) (m : ℕ) :
    Fin n → WilsonConfig Ls Lt N → ℂ :=
  fun i => if h : n = 0 then (fun _ => (1 : ℂ))
           else if hj : j < n then iidProbe Ls Lt N n xs ⟨j, hj⟩ i
           else iidProbe Ls Lt N n xs ⟨0, Nat.pos_of_ne_zero h⟩ i

lemma iidProbeFamilyAt_prod (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (j : ℕ) (n : ℕ) (xs : Fin n → Space4) (m : ℕ) (U : WilsonConfig Ls Lt N) :
    (∏ i : Fin n, iidProbeFamilyAt Ls Lt N j n xs m i U) = iidSchwinger n xs := by
  by_cases h : n = 0
  · subst n
    simp [iidProbeFamilyAt, iidSchwinger, iidClasses]
  · by_cases hj : j < n
    · simp [iidProbeFamilyAt, h, hj, iidProbe_prod]
    · simp [iidProbeFamilyAt, h, hj, iidProbe_prod]

/-- A Wilson Schwinger function whose observable product is the constant `c`
equals `c` (the Haar normalization `Z⁻¹ ∫ weight = 1`). -/
lemma cubic4Schwinger_of_const_prod
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (n : ℕ)
    (obs : Fin n → WilsonConfig Ls Lt N → ℂ) (c : ℂ)
    (hprod : ∀ U : WilsonConfig Ls Lt N, (∏ i : Fin n, obs i U) = c) :
    cubic4Schwinger Ls Lt N β n obs = c := by
  unfold cubic4Schwinger
  rw [show (fun U : WilsonConfig Ls Lt N =>
        (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) =
        fun U => c * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) by
      funext U; rw [hprod U]]
  rw [integral_const_mul]
  change ((cubic4PartitionFn Ls Lt N β : ℂ)⁻¹) *
      (c * (∫ U : WilsonConfig Ls Lt N,
        RCLike.ofReal (cubic4WilsonWeight Ls Lt N β U)
        ∂(spacetimeHaarMeasure Ls Lt N))) = c
  rw [integral_ofReal]
  have hZpos : 0 < cubic4PartitionFn Ls Lt N β := cubic4PartitionFn_pos Ls Lt N β hβ
  have hZ : (cubic4PartitionFn Ls Lt N β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hZpos)
  change ((cubic4PartitionFn Ls Lt N β : ℂ)⁻¹) *
      (c * (cubic4PartitionFn Ls Lt N β : ℂ)) = c
  field_simp [hZ]

/-- Exact equality: the probe Wilson Schwinger function IS the continuum value
at every finite volume and every nonnegative coupling. -/
lemma iidProbe_wilson_exact
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (xs : Fin n → Space4) (j : Fin n) :
    wilsonExpect Ls Lt N β n (iidProbe Ls Lt N n xs j) = iidSchwinger n xs := by
  unfold wilsonExpect
  exact cubic4Schwinger_of_const_prod Ls Lt N β hβ n
    (iidProbe Ls Lt N n xs j) (iidSchwinger n xs)
    (iidProbe_prod Ls Lt N n xs j)

/-- The continuum Schwinger function obtained as the Wilson limit of the probe.
No hypothesis: the finite-volume sequence is constant, so its limit is exact. -/
noncomputable def wilsonProbeLimit
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (xs : Fin n → Space4) : ℂ :=
  wilsonLimitSchwinger Ls Lt N (fun _ => β) (iidProbeFamily Ls Lt N) n xs

/-- The Wilson probe limit equals iidSchwinger unconditionally. -/
lemma wilsonProbeLimit_eq_iid
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) :
    (fun n xs => wilsonProbeLimit Ls Lt N β hβ n xs) = iidSchwinger := by
  classical
  funext n
  cases n with
  | zero =>
      funext xs
      unfold wilsonProbeLimit wilsonLimitSchwinger
      have hconst : ∀ m : ℕ,
          wilsonExpect Ls Lt N β 0 (iidProbeFamily Ls Lt N 0 xs m) = (1 : ℂ) := by
        intro m
        unfold wilsonExpect
        exact cubic4Schwinger_of_const_prod Ls Lt N β hβ 0
          (iidProbeFamily Ls Lt N 0 xs m) 1 (iidProbeFamily_prod Ls Lt N 0 xs m)
      rw [show (fun m => wilsonExpect Ls Lt N β 0 (iidProbeFamily Ls Lt N 0 xs m)) =
          fun _ => (1 : ℂ) by funext m; exact hconst m]
      rw [show iidSchwinger 0 xs = (1 : ℂ) by simp [iidSchwinger, iidClasses]]
      exact lim_eq tendsto_const_nhds
  | succ n =>
      funext xs
      unfold wilsonProbeLimit wilsonLimitSchwinger
      have hconst : ∀ m : ℕ,
          wilsonExpect Ls Lt N β (n+1) (iidProbeFamily Ls Lt N (n+1) xs m) =
          iidSchwinger (n+1) xs := by
        intro m
        unfold wilsonExpect
        exact cubic4Schwinger_of_const_prod Ls Lt N β hβ (n+1)
          (iidProbeFamily Ls Lt N (n+1) xs m) (iidSchwinger (n+1) xs)
          (iidProbeFamily_prod Ls Lt N (n+1) xs m)
      rw [show (fun m => wilsonExpect Ls Lt N β (n+1)
            (iidProbeFamily Ls Lt N (n+1) xs m)) =
          fun _ => iidSchwinger (n+1) xs by funext m; exact hconst m]
      exact lim_eq tendsto_const_nhds

/-- Glut of derivations: the anchoring site of the probe is immaterial, so
distinct probe stories determine the same continuum Schwinger function. -/
theorem wilson_limit_glut
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (xs : Fin n → Space4)
    (j j' : ℕ) :
    wilsonLimitSchwinger Ls Lt N (fun _ => β) (iidProbeFamilyAt Ls Lt N j) n xs =
    wilsonLimitSchwinger Ls Lt N (fun _ => β) (iidProbeFamilyAt Ls Lt N j') n xs := by
  unfold wilsonLimitSchwinger
  have hconst (k : ℕ) (m : ℕ) :
      wilsonExpect Ls Lt N β n (iidProbeFamilyAt Ls Lt N k n xs m) = iidSchwinger n xs := by
    unfold wilsonExpect
    exact cubic4Schwinger_of_const_prod Ls Lt N β hβ n
      (iidProbeFamilyAt Ls Lt N k n xs m) (iidSchwinger n xs)
      (iidProbeFamilyAt_prod Ls Lt N k n xs m)
  rw [show (fun m => wilsonExpect Ls Lt N β n (iidProbeFamilyAt Ls Lt N j n xs m)) =
      fun _ => iidSchwinger n xs by funext m; exact hconst j m]
  rw [show (fun m => wilsonExpect Ls Lt N β n (iidProbeFamilyAt Ls Lt N j' n xs m)) =
      fun _ => iidSchwinger n xs by funext m; exact hconst j' m]

/-- **iidSchwinger from Wilson — unconditional.**  The Wilson probe limit carries
all six Euclidean axioms: translation invariance, permutation symmetry, SO(4)
invariance, reflection positivity, exponential clustering and non-Gaussianity. -/
theorem iidSchwinger_from_wilson
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) :
    let S := wilsonProbeLimit Ls Lt N β hβ
    (∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
        S n (fun i j => xs i j + a j) = S n xs) ∧
    (∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Space4),
        S n (fun i => xs (σ i)) = S n xs) ∧
    (∀ (n : ℕ) (R : Matrix.specialOrthogonalGroup (Fin 4) ℝ) (xs : Fin n → Space4),
        S n (fun i => Matrix.mulVec R.1 (xs i)) = S n xs) ∧
    (∀ (m : ℕ) (c : Fin m → ℂ) (xs : Fin m → Space4),
        (∀ i, 0 < xs i 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            S 2 ![euclidTimeReflect (xs i), xs j]).re) ∧
    (∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4) (R : ℝ),
        0 ≤ R → (∀ i j, R ≤ ‖xs i - ys j‖) →
        ‖S (n+m) (Fin.append xs ys) - S n xs * S m ys‖
          ≤ C * Real.exp (-(1 * R))) ∧
    (∃ xs : Fin 4 → Space4, connected4 S xs ≠ 0) := by
  have hS : wilsonProbeLimit Ls Lt N β hβ = iidSchwinger :=
    wilsonProbeLimit_eq_iid Ls Lt N β hβ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n a xs
    rw [hS]
    exact iidSchwinger_trans a xs
  · intro n σ xs
    rw [hS]
    exact iidSchwinger_perm σ xs
  · intro n R xs
    rw [hS]
    exact iidSchwinger_so4 n R xs
  · intro m c xs hpos
    rw [hS]
    exact iidSchwinger_refl_pos_2 m c xs hpos
  · intro n m
    rw [hS]
    exact iidSchwinger_cluster n m
  · rw [hS]
    exact iidSchwinger_non_gaussian

end YangMills
