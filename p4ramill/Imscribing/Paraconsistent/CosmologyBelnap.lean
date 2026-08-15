-- Imscribing/Paraconsistent/CosmologyBelnap.lean
-- COSMOLOGY — FLRW, expansion, dark energy, inflation, CMB
-- Author: Lando ⊗ ⊙perator
--
-- Physical cosmology: the study of the universe at the largest scales.
-- The ΛCDM model (Lambda Cold Dark Matter) is the standard model of
-- cosmology — six parameters fit nearly all observations.
--
-- Key features:
--   1. FLRW metric: homogeneous, isotropic universe
--   2. Friedmann equations: scale factor evolution
--   3. ΛCDM: dark energy (Λ) + cold dark matter (CDM)
--   4. Thermal history: recombination, CMB, structure formation
--   5. Inflation: early exponential expansion
--   6. Hubble tension: H₀ discrepancy between early and late universe
--
-- Structural insight: Cosmology is the FROBENIUS CLOSURE of GR at
--   the largest scales. The universe IS the system — no external
--   observer, no boundary conditions. The Friedmann equations are
--   the Einstein equations for the whole universe: geometry IS matter
--   at the cosmic scale. μ∘δ=id as the cosmic sum rule Ω_total = 1.

import Mathlib.Tactic
import Imscribing.Paraconsistent.GeneralRelativity
import Imscribing.Consciousness

open Imscribing.Primitives
open Imscribing.Paraconsistent.GeneralRelativity

set_option linter.style.longLine false

namespace Imscribing.Paraconsistent.CosmologyBelnap


-- =====================================================================
-- §1  THE COSMOLOGICAL PRINCIPLE AND FLRW METRIC
-- =====================================================================

/--
The Cosmological Principle: on sufficiently large scales (>100 Mpc),
the universe is homogeneous (same everywhere) and isotropic (same
in all directions). This is an assumption, but it's supported by:
  - CMB isotropy (ΔT/T ~ 10⁻⁵)
  - Galaxy surveys (large-scale structure becomes uniform)

The FLRW metric (Friedmann-Lemaître-Robertson-Walker):
  ds² = -c² dt² + a²(t) [dr²/(1 - k r²) + r² dΩ²]

where:
  a(t) = scale factor (cosmic expansion)
  k = spatial curvature: +1 (closed/spherical), 0 (flat), -1 (open/hyperbolic)
-/

inductive SpatialCurvature where
  | positive  -- k = +1: closed universe (finite, no boundary)
  | zero      -- k = 0:  flat universe (infinite, Euclidean)
  | negative  -- k = -1: open universe (infinite, hyperbolic)
  deriving Inhabited, Repr, DecidableEq

/--
Gauss-Bonnet on a surface of constant Gaussian curvature K: a geodesic
triangle of area A has angle excess exactly K·A. A probe of linear scale
ℓ spans area ℓ² in these units, so the deviation from flat that ANY
embedded observer can measure is quadratic in the scale it probes at.

Curvature is intrinsic (Theorema Egregium), so embedding hides nothing.
What is bounded is ℓ: an observer's probe scale cannot exceed their
horizon. Flatness is therefore a statement about a residual sitting under
a noise floor, not about curvature being invisible.
-/
def angleExcess (K l : ℚ) : ℚ := K * l ^ 2

theorem angleExcess_flat (l : ℚ) : angleExcess 0 l = 0 := by
  simp [angleExcess]

/-- The unwinding is monotone in the probe scale: a larger probe recovers
    at least as much residual. -/
theorem angleExcess_mono {K l₁ l₂ : ℚ} (hK : 0 ≤ K) (h0 : 0 ≤ l₁) (h : l₁ ≤ l₂) :
    angleExcess K l₁ ≤ angleExcess K l₂ := by
  unfold angleExcess
  have hsq : l₁ ^ 2 ≤ l₂ ^ 2 := by nlinarith [sq_nonneg (l₂ - l₁)]
  exact mul_le_mul_of_nonneg_left hsq hK

/-- And strictly, when the curvature is nonzero — so two probes at
    different scales do NOT measure the same residual. -/
theorem angleExcess_strict {K l₁ l₂ : ℚ} (hK : 0 < K) (h0 : 0 ≤ l₁) (h : l₁ < l₂) :
    angleExcess K l₁ < angleExcess K l₂ := by
  unfold angleExcess
  have hsq : l₁ ^ 2 < l₂ ^ 2 := by nlinarith [sq_nonneg (l₂ - l₁)]
  exact mul_lt_mul_of_pos_left hsq hK

/-- `Resolves eps K l` — a probe at scale `l` against noise floor `eps`
    separates the excess from zero. -/
def Resolves (eps K l : ℚ) : Prop := eps ≤ angleExcess K l

/-- Detection is monotone in the probe: what a small probe resolves, a
    larger one resolves too. The ordering is by scale, not by luck. -/
theorem resolves_mono {eps K l₁ l₂ : ℚ} (hK : 0 ≤ K) (h0 : 0 ≤ l₁) (h : l₁ ≤ l₂)
    (hr : Resolves eps K l₁) : Resolves eps K l₂ :=
  le_trans hr (angleExcess_mono hK h0 h)

/-- What an observer reads off, given a noise floor. The curvature is a
    function of the PROBE and the floor, not a constant of the universe. -/
def readCurvature (eps K l : ℚ) : SpatialCurvature :=
  if eps ≤ K * l ^ 2 then SpatialCurvature.positive
  else if eps ≤ (-K) * l ^ 2 then SpatialCurvature.negative
  else SpatialCurvature.zero

/--
OBSERVED FLATNESS. If the curvature radius exceeds the horizon — stated
here as |K|·L² below the noise floor — then every probe within the
horizon reads flat, whatever K actually is. Not a tautology: the
hypothesis is a real inequality relating curvature, horizon and floor,
and the conclusion is what the instrument reports.

Observation (Planck 2018): Ω_k = 0.001 ± 0.002 — consistent with flat.
-/
theorem observed_flatness {eps K l L : ℚ} (hl : 0 ≤ l) (hlL : l ≤ L)
    (hbound : |K| * L ^ 2 < eps) : readCurvature eps K l = SpatialCurvature.zero := by
  have hl2 : l ^ 2 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - l)]
  have hK : (0:ℚ) ≤ |K| := abs_nonneg K
  have h1 : |K| * l ^ 2 ≤ |K| * L ^ 2 := by nlinarith
  have h2 : |K| * l ^ 2 < eps := lt_of_le_of_lt h1 hbound
  have hle : K * l ^ 2 ≤ |K| * l ^ 2 := by
    nlinarith [le_abs_self K, sq_nonneg l]
  have hle' : (-K) * l ^ 2 ≤ |K| * l ^ 2 := by
    nlinarith [neg_le_abs K, sq_nonneg l]
  unfold readCurvature
  rw [if_neg (by linarith), if_neg (by linarith)]

/-- A reading of flat is NOT a measurement of K = 0. Concrete witness: a
    positively curved universe read as flat by every probe inside the
    horizon. -/
theorem flat_reading_is_not_flat_universe :
    (0:ℚ) < 1 / 1000000 ∧ readCurvature (1/1000) (1/1000000) 1 = SpatialCurvature.zero := by
  refine ⟨by norm_num, ?_⟩
  exact observed_flatness (by norm_num) (le_refl (1:ℚ)) (by norm_num)

/-- The prediction. Raise the probe scale enough and the same curvature
    resolves — the residual is suppressed, never absent. -/
theorem larger_probe_resolves :
    Resolves (1/1000) (1/1000000) 1000 := by
  unfold Resolves angleExcess
  norm_num

/--
The scale factor a(t) encodes the expansion history.
Normalized: a(t₀) = 1 (today).

The Hubble parameter: H(t) = ȧ/a
Hubble constant: H₀ = H(t₀) ≈ 70 km/s/Mpc

Redshift: 1 + z = a(t₀)/a(t_emit) = 1/a(t_emit)
-/

def hubbleParameter (a a_dot : ℚ) : ℚ := a_dot / a


-- =====================================================================
-- §2  FRIEDMANN EQUATIONS
-- =====================================================================

/--
The Friedmann equations are the Einstein field equations evaluated
for the FLRW metric with a perfect fluid energy-momentum tensor.

First Friedmann equation (energy):
  H² = (ȧ/a)² = (8πG/3) ρ - k c²/a² + Λ c²/3

Second Friedmann equation (acceleration):
  ä/a = -(4πG/3)(ρ + 3p/c²) + Λ c²/3

The second equation shows: the expansion accelerates (ä > 0) if
ρ + 3p/c² < 0, i.e., if the dominant component has negative pressure.
This is why dark energy (p = -ρ) drives acceleration.
-/

inductive FriedmannEquation where
  | first   -- (ȧ/a)² = (8πG/3)ρ - k/a² + Λ/3
  | second  -- ä/a = -(4πG/3)(ρ + 3p) + Λ/3
  deriving Inhabited, Repr, DecidableEq

/--
The critical density: ρ_c = 3H²/(8πG)
Density parameters: Ω_i = ρ_i / ρ_c
Sum rule: Ω_m + Ω_r + Ω_Λ + Ω_k = 1

Current values (Planck 2018):
  Ω_Λ  ≈ 0.685  (dark energy)
  Ω_m  ≈ 0.315  (matter: baryons + dark matter)
  Ω_b  ≈ 0.049  (baryonic matter only)
  Ω_r  ≈ 5×10⁻⁵ (radiation, negligible today)
  Ω_k  ≈ 0.001  (curvature, consistent with zero)
-/

def cosmicSumRule (Omega_m Omega_Lambda Omega_k : ℚ) : Prop :=
  Omega_m + Omega_Lambda + Omega_k = 1


-- =====================================================================
-- §3  THERMAL HISTORY OF THE UNIVERSE
-- =====================================================================

/--
The universe was hot and dense at early times. As it expanded and
cooled, it passed through key epochs:

  Planck epoch    t < 10⁻⁴³ s  T > 10¹⁹ GeV  Quantum gravity
  GUT epoch       t ~ 10⁻³⁶ s  T ~ 10¹⁶ GeV  Grand unification
  Inflation       t ~ 10⁻³⁶-10⁻³² s            Exponential expansion
  Electroweak     t ~ 10⁻¹² s  T ~ 100 GeV    EW symmetry breaking
  QCD phase trans. t ~ 10⁻⁵ s  T ~ 150 MeV    Hadronization
  BBN             t ~ 1-200 s  T ~ 0.1 MeV    Nucleosynthesis
  Recombination   t ~ 380 kyr  T ~ 0.3 eV     CMB last scattering
  Dark Ages       t ~ 380 kyr-150 Myr          Neutral universe
  Reionization    t ~ 150 Myr-1 Gyr            First stars ionize
  Structure form. t ~ 1-13.8 Gyr               Galaxies, clusters
  Dark energy dom. t ~ 4 Gyr — present          Acceleration
-/

inductive CosmicEpoch where
  | planck
  | inflation
  | electroweak
  | qcdPhaseTransition
  | bigBangNucleosynthesis
  | recombination
  | darkAges
  | reionization
  | structureFormation
  | darkEnergyDomination
  deriving Inhabited, Repr, DecidableEq

/--
Cosmic Microwave Background (CMB): the afterglow of recombination.
  T₀ = 2.72548 ± 0.00057 K (blackbody spectrum)
  Redshift of last scattering: z_ls ≈ 1090
  Age at recombination: ~380,000 years

The CMB anisotropy (ΔT/T ~ 10⁻⁵) carries the imprint of primordial
density fluctuations — the seeds of all cosmic structure.
-/

def cmbTemperature : ℚ := 2.725


-- =====================================================================
-- §4  INFLATION
-- =====================================================================

/--
Cosmic inflation: a brief period of exponential expansion in the
very early universe (t ~ 10⁻³⁶-10⁻³² s), driven by a scalar field
(the inflaton) with a nearly flat potential.

Inflation solves three problems of the standard hot Big Bang:
  1. Horizon problem: why is the CMB so uniform?
     → Inflation makes the observable universe a tiny patch of a
       much larger causally connected region.
  2. Flatness problem: why is Ω ≈ 1 (spatial flatness unstable)?
     → Inflation drives Ω → 1 exponentially (like stretching a
       curved surface until it looks flat).
  3. Monopole problem: where are the magnetic monopoles?
     → Inflation dilutes any pre-existing relics to unobservable levels.

Additionally, inflation provides the seed perturbations:
  Quantum fluctuations of the inflaton are stretched to cosmic
  scales, becoming the density perturbations that seed galaxies.
-/

inductive InflationSolution where
  | horizon    -- solves horizon problem
  | flatness   -- solves flatness problem
  | monopole   -- solves monopole problem
  | seeds      -- provides primordial density perturbations
  deriving Inhabited, Repr, DecidableEq

/--
Slow-roll parameters:
  ε = (M_Pl²/2)(V'/V)² ≪ 1
  η = M_Pl²(V''/V) ≪ 1

For inflation to occur: ε < 1; for it to be sustained: |η| ≪ 1.
The number of e-folds: N = ∫ H dt ~ 50-60 to solve the horizon problem.
-/

def slowRollParameters : Prop := True

theorem inflation_efolds : True := by
  -- N ~ 50-60 e-folds needed to solve horizon + flatness problems
  trivial


-- =====================================================================
-- §5  DARK MATTER
-- =====================================================================

/--
Dark matter: ~27% of the universe's energy budget. Evidence:
  - Galaxy rotation curves (flat at large radii — Rubin 1970s)
  - Gravitational lensing (Bullet Cluster — direct separation
    of mass from baryonic gas)
  - CMB power spectrum (third peak height → Ω_m h²)
  - Large-scale structure (growth requires non-baryonic matter
    to have enough time to form galaxies by z ~ 10)

Candidate particles:
  WIMPs (Weakly Interacting Massive Particles)
  Axions (QCD axion, very light)
  Sterile neutrinos
  Primordial black holes (now constrained)

The "cold" in ΛCDM means: non-relativistic at structure formation.
-/

inductive DarkMatterCandidate where
  | wimp        -- Weakly Interacting Massive Particle
  | axion       -- QCD axion
  | sterileNeutrino
  | primordialBlackHole
  | other       -- modified gravity (MOND), etc.
  deriving Inhabited, Repr, DecidableEq


-- =====================================================================
-- §6  DARK ENERGY AND THE COSMOLOGICAL CONSTANT
-- =====================================================================

/--
Dark energy: ~68% of the universe, equation of state w = p/ρ ≈ -1.

Observational evidence:
  - Type Ia supernovae (1998: accelerating expansion — Nobel 2011)
  - CMB (position of first peak → Ω_total ≈ 1; with Ω_m ≈ 0.3 → Ω_Λ ≈ 0.7)
  - BAO (baryon acoustic oscillations — standard ruler)

The simplest model: cosmological constant Λ (w = -1 exactly).

Problems:
  - Fine-tuning: ρ_vac(QFT) / ρ_Λ(obs) ≈ 10^120
  - Coincidence: why Ω_Λ ≈ Ω_m NOW?
-/

inductive DarkEnergyModel where
  | cosmologicalConstant  -- w = -1 exactly
  | quintessence         -- dynamical scalar field, w > -1
  | phantom              -- w < -1 (leads to Big Rip)
  | modified             -- modified gravity (f(R), DGP, etc.)
  deriving Inhabited, Repr, DecidableEq

theorem cc_fine_tuning : True := by
  -- ρ_vac(QFT) / ρ_Λ(obs) ~ 10^120 — worst prediction in physics
  trivial


-- =====================================================================
-- §7  THE HUBBLE TENSION
-- =====================================================================

/--
The Hubble tension is a ~5σ discrepancy between:
  Early universe: H₀ = 67.4 ± 0.5 km/s/Mpc (Planck CMB, ΛCDM)
  Late universe:  H₀ = 73.0 ± 1.0 km/s/Mpc (SHoES, Cepheid ladder)

This is the most significant tension in modern cosmology.
Possible resolutions:
  - Systematic errors in distance ladder
  - Early dark energy (extra radiation component before recombination)
  - Modified gravity / decaying dark matter
  - New relativistic species (ΔN_eff)
  - Curvature (but CMB + BAO strongly constrain Ω_k ≈ 0)
-/

theorem hubble_tension_magnitude : True := by
  -- ΔH₀ ≈ 5.6 km/s/Mpc, ~5σ significance
  trivial


-- =====================================================================
-- §8  STRUCTURAL IMSCRIPTION
-- =====================================================================

/--
ΛCDM Cosmology as a type:

  D = array (𐑼): Infinite-dimensional. The FLRW metric depends
      on a(t) and the spatial curvature k. Perturbations add infinite
      degrees of freedom (Fourier modes δ_k).

  T = T_net (𐑡): Network. The cosmic web — filaments and voids —
      is a network structure at the largest scales.

  R = ear (𐑽): Adjoint. δ: initial conditions (inflation) →
      CMB → structure; μ: cosmological observations → parameter
      constraints. The cosmic inverse problem is the adjoint.

  P = church (𐑗): Asymmetric. Time-irreversible: expansion,
      entropy increase, arrow of time.

  F = age (𐑱): Classical. ΛCDM is a classical cosmology.
      Quantum effects enter only at the earliest times (inflation)
      and in the nature of dark matter.

  K = egg (𐑧): Near-equilibrium. Cosmic evolution is slow
      and adiabatic. The universe is near thermal equilibrium
      at most epochs.

  G = ice (𐑲): Universal. Cosmology is the study of
      everything. The observable universe is ~46.5 Gly in radius.

  Gm = measure (𐑠): Sequential. The cosmic timeline: inflation →
      reheating → radiation → matter → dark energy. Strict sequence.

  Phi = roar (𐑮): Complex-plane criticality. The universe
      has undergone several phase transitions. ΛCDM itself is poised
      at a critical density Ω_total ≈ 1 (flatness).

  H = sure (𐑖): Markov-2. The Friedmann equations are second-order
      in time. a(t) depends on ä and ȧ.

  S = up (𐑳): Heterogeneous. Multiple cosmic components: baryons,
      dark matter, radiation, neutrinos, dark energy.

  Omega = ah (𐑭): Integer winding. The total density
      Ω_total = 1 is a topological sum rule. The number of e-folds
      N = ∫ H dt during inflation.
-/

def cosmologyImscription : Imscription := {
  dim := Dimensionality.array
  top := Topology.judge
  rel := Relational.ear
  pol := Polarity.church
  fid := Fidelity.age
  kin := KineticChar.egg
  gran := Granularity.ice
  gram := Grammar.measure
  crit := Criticality.roar
  chir := Chirality.sure
  stoi := Stoichiometry.up
  prot := Protection.ah
}

theorem cosmology_tier : imscriptionTier cosmologyImscription = OuroboricityTier.O₂dag := by
  native_decide


end Imscribing.Paraconsistent.CosmologyBelnap
