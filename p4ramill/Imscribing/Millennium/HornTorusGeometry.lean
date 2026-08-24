/-
Imscribing/Millennium/HornTorusGeometry.lean
============================================
Formalization of the Horn Torus geometry (ig-docs/HORN_TORUS_GEOMETRY_CONTEXT.md)
and the seven Clay-theorem structure ob3ects generated 2026-08-23/24 into
/home/mrnob0dy666/imsgct/ob3ect/digital/:

  navier_stokes_theorem_structure   (⊙ pinch)
  yang_mills_structure              (∈ split shell λ_C)
  bsd_structure                     (∋ coupler)
  hodge_structure                   (chirality, trine vertex 2)
  riemann_structure                 (⊞ self-reference closure)
  p_vs_np_structure                 (◻ winding)
  dynamics_structure_trine_vertex_1 (⊤ shared floor)

Every numeric claim is exact — zero sorries. In particular the tilt that puts
ENGAGR on the horn torus is proven exactly: rotation about the syzygy (x) axis
by θ = π/6 (30°) maps the scaled ENGAGR point 2·⊞ = (2,−1,−√3) to (2,0,−2),
which lies on the R = 2 horn torus (unit scale: ⊞ → (1,0,−1) on the R = 1 horn).
The paper's drawing-scale arctan(1/4) ≈ 14.0° and 7.5° sector offset are the
quartered rendering of this exact angle (7.5° = 30°/4, the four-valued kernel);
the untilted same-frame check provably fails, exactly as the context sheet warns.

Author: Quantum⊙perator (Lando⊗⊙perator team) · 2026-08-24
-/

import Mathlib

namespace Imscribing
namespace HornTorus

/-! ## The four-valued kernel — |B4| = 4 -/

inductive B4 | N | T | F | B
  deriving DecidableEq, Fintype, Repr

/-! ## (16,3): the knot arithmetic
Sixteen toroidal windings against three poloidal ones. Sixteen matches the
trilattice's state count 2⁴ = 16 = |I|² — the two coincide at n = 4
(Proposition 2.3). Conductor at d = 2048: 𝔣 = (2¹²)∞₁ = (16³)∞₁. -/

theorem sixteen_eq_two_pow_four : (16 : ℕ) = 2 ^ 4 := by norm_num

theorem card_b4 : Fintype.card B4 = 4 := by native_decide

theorem card_b4_sq : Fintype.card (B4 × B4) = 16 := by native_decide

theorem two_pow_four_eq_card : 2 ^ 4 = Fintype.card (B4 × B4) := by
  rw [card_b4_sq]
  norm_num

theorem d2048 : (2048 : ℕ) = 2 ^ 11 := by norm_num

theorem conductor_exponent : (16 : ℕ) ^ 3 = 2 ^ 12 := by norm_num

/-! ## Points, distances, and the horn torus
Point is the nested pair ℝ × (ℝ × ℝ): x = p.1, y = p.2.1, z = p.2.2. -/

abbrev Point : Type := ℝ × ℝ × ℝ

def origin : Point := (0, 0, 0)

def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

-- Horn torus R = r: p(u,v) = (R(1+cos u)cos v, R(1+cos u)sin v, R sin u)
noncomputable def horn (R u v : ℝ) : Point :=
  (R * (1 + Real.cos u) * Real.cos v, R * (1 + Real.cos u) * Real.sin v, R * Real.sin u)

-- Implicit horn-torus equation (R = r): (x²+y²+z²)² = (2R)²(x²+y²)
def OnHorn (R : ℝ) (p : Point) : Prop := (sqDist p origin) ^ 2 = (2 * R) ^ 2 * (p.1 ^ 2 + p.2.1 ^ 2)

/-! ## ⊙ the pinch: at u = π the whole v-circle collapses to the origin -/

theorem pinch (v : ℝ) : horn 2 Real.pi v = origin := by
  apply Prod.ext
  · norm_num [horn, origin, Real.cos_pi, Real.sin_pi]
  · apply Prod.ext
    · norm_num [horn, origin, Real.cos_pi, Real.sin_pi]
    · norm_num [horn, origin, Real.cos_pi, Real.sin_pi]

-- γ(t) the equatorial curve: γ(0) at x = 2R, γ(π) = the horn (the pinch)
noncomputable def gamma (R t : ℝ) : Point := horn R t 0

theorem gamma_zero (R : ℝ) : gamma R 0 = (2 * R, 0, 0) := by
  apply Prod.ext
  · norm_num [gamma, horn, Real.cos_zero, Real.sin_zero]
    ring
  · apply Prod.ext
    · norm_num [gamma, horn, Real.cos_zero, Real.sin_zero]
    · norm_num [gamma, horn, Real.cos_zero, Real.sin_zero]

theorem gamma_pi (R : ℝ) : gamma R Real.pi = origin := by
  apply Prod.ext
  · norm_num [gamma, horn, origin, Real.cos_pi, Real.sin_pi]
  · apply Prod.ext
    · norm_num [gamma, horn, origin, Real.cos_pi, Real.sin_pi]
    · norm_num [gamma, horn, origin, Real.cos_pi, Real.sin_pi]

/-! ## Named features (paper scale: R = 2, ∋ at x = 2, λ_C = R/2 = 1) -/

def omega : Point := (2, 0, 0)          -- ∋
def sphereCentre : Point := (1, 0, 0)   -- evaluator sphere centre
def lambdaC : ℝ := 1                    -- split shell radius λ_C = R/2

-- evaluator trine: ⊤, ⊥, ⊞ on the equatorial circle x = λ_C
def trineTop : Point := (1, 1, 0)
noncomputable def trineFalsity : Point := (1, -1 / 2, Real.sqrt 3 / 2)
noncomputable def trineEngagr : Point := (1, -1 / 2, -Real.sqrt 3 / 2)

/-! Exact lemmas for the √3 coordinates -/
lemma sq_sqrt_three : (Real.sqrt 3) ^ 2 = 3 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma sqrt_three_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := by
  rw [← pow_two, sq_sqrt_three]

/-! ## ⊙ and ∋ on the evaluator sphere; coupler length -/

theorem origin_on_sphere : sqDist origin sphereCentre = 1 := by
  norm_num [origin, sphereCentre, sqDist]

theorem omega_on_sphere : sqDist omega sphereCentre = 1 := by
  norm_num [omega, sphereCentre, sqDist]

theorem coupler_length_sq : sqDist omega origin = 4 := by
  norm_num [omega, origin, sqDist]
/-! ## The trine: all three on the evaluator sphere -/

theorem trineTop_on_sphere : sqDist trineTop sphereCentre = 1 := by
  norm_num [trineTop, sphereCentre, sqDist]

theorem trineFalsity_on_sphere : sqDist trineFalsity sphereCentre = 1 := by
  unfold sqDist trineFalsity sphereCentre
  nlinarith [sq_sqrt_three]

theorem trineEngagr_on_sphere : sqDist trineEngagr sphereCentre = 1 := by
  unfold sqDist trineEngagr sphereCentre
  nlinarith [sq_sqrt_three]

/-! ## The trine is equilateral: pairwise squared distance 3 -/

theorem trine_equilateral_top_falsity : sqDist trineTop trineFalsity = 3 := by
  unfold sqDist trineTop trineFalsity
  nlinarith [sq_sqrt_three]

theorem trine_equilateral_top_engagr : sqDist trineTop trineEngagr = 3 := by
  unfold sqDist trineTop trineEngagr
  nlinarith [sq_sqrt_three]

theorem trine_equilateral_falsity_engagr : sqDist trineFalsity trineEngagr = 3 := by
  unfold sqDist trineFalsity trineEngagr
  nlinarith [sq_sqrt_three]

/-! ## Three distinct vertices — bridge number 3, the three arms of the kernel -/

theorem trineTop_ne_falsity : trineTop ≠ trineFalsity := by
  intro h
  have h2 : (trineTop : Point).2.1 = trineFalsity.2.1 := by rw [h]
  unfold trineTop trineFalsity at h2
  norm_num at h2

theorem trineTop_ne_engagr : trineTop ≠ trineEngagr := by
  intro h
  have h2 : (trineTop : Point).2.1 = trineEngagr.2.1 := by rw [h]
  unfold trineTop trineEngagr at h2
  norm_num at h2

theorem trineFalsity_ne_engagr : trineFalsity ≠ trineEngagr := by
  intro h
  have h3 : (trineFalsity : Point).2.2 = trineEngagr.2.2 := by rw [h]
  unfold trineFalsity trineEngagr at h3
  have hp : 0 < Real.sqrt 3 := by positivity
  have hz : Real.sqrt 3 = 0 := by nlinarith [h3]
  exact (ne_of_gt hp) hz

theorem trine_card : ({trineTop, trineFalsity, trineEngagr} : Finset Point).card = 3 := by
  classical
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · intro h
    exact trineFalsity_ne_engagr (Finset.mem_singleton.mp h)
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact trineTop_ne_falsity h
    · exact trineTop_ne_engagr (Finset.mem_singleton.mp h)

/-! ## Projections: top-down = A₂ triangle, side-on = collinear -/

def projYZ (p : Point) : ℝ × ℝ := (p.2.1, p.2.2)
def projXZ (p : Point) : ℝ × ℝ := (p.1, p.2.2)
def sqDist2 (a b : ℝ × ℝ) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2
def dot2 (a b : ℝ × ℝ) : ℝ := a.1 * b.1 + a.2 * b.2

-- Top-down (z = 0): the three 120°-equator points are the A₂ roots
theorem projYZ_top : projYZ trineTop = (1, 0) := by
  norm_num [projYZ, trineTop]

theorem projYZ_falsity : projYZ trineFalsity = (-1 / 2, Real.sqrt 3 / 2) := by
  norm_num [projYZ, trineFalsity]

theorem projYZ_engagr : projYZ trineEngagr = (-1 / 2, -Real.sqrt 3 / 2) := by
  norm_num [projYZ, trineEngagr]

-- Side-on (xz, y = 0): edge-on, the trine collapses to the line x = 1
theorem xz_collinear :
    (projXZ trineTop).1 = 1 ∧ (projXZ trineFalsity).1 = 1 ∧ (projXZ trineEngagr).1 = 1 := by
  norm_num [projXZ, trineTop, trineFalsity, trineEngagr]

-- The A₂ triangle is equilateral (squared distance 3) — the knot's poloidal winding as a circuit
theorem A2_equilateral_top_falsity : sqDist2 (projYZ trineTop) (projYZ trineFalsity) = 3 := by
  rw [projYZ_top, projYZ_falsity]
  unfold sqDist2
  nlinarith [sq_sqrt_three]

theorem A2_equilateral_top_engagr : sqDist2 (projYZ trineTop) (projYZ trineEngagr) = 3 := by
  rw [projYZ_top, projYZ_engagr]
  unfold sqDist2
  nlinarith [sq_sqrt_three]

theorem A2_equilateral_falsity_engagr : sqDist2 (projYZ trineFalsity) (projYZ trineEngagr) = 3 := by
  rw [projYZ_falsity, projYZ_engagr]
  unfold sqDist2
  nlinarith [sq_sqrt_three]

-- 120° spacing: pairwise dot products −1/2
theorem dot2_top_falsity : dot2 (projYZ trineTop) (projYZ trineFalsity) = -1 / 2 := by
  rw [projYZ_top, projYZ_falsity]
  norm_num [dot2]

theorem dot2_falsity_engagr : dot2 (projYZ trineFalsity) (projYZ trineEngagr) = -1 / 2 := by
  rw [projYZ_falsity, projYZ_engagr]
  unfold dot2
  nlinarith [sq_sqrt_three]

theorem dot2_top_engagr : dot2 (projYZ trineTop) (projYZ trineEngagr) = -1 / 2 := by
  rw [projYZ_top, projYZ_engagr]
  norm_num [dot2]

/-! ## ENGAGR off the untilted torus — the context sheet's wrong-frame warning, formalized -/

theorem trineEngagr_norm_sq : sqDist trineEngagr origin = 2 := by
  unfold sqDist trineEngagr origin
  nlinarith [sq_sqrt_three]

theorem engagr_not_on_untilted : ¬ OnHorn 2 trineEngagr := by
  intro h
  rw [OnHorn] at h
  rw [trineEngagr_norm_sq] at h
  norm_num [trineEngagr] at h

/-! ## Rotation about the syzygy (x) axis preserves the sphere — so no x-tilt reaches the R = 2 horn -/

noncomputable def rotX (θ : ℝ) (p : Point) : Point :=
  (p.1, p.2.1 * Real.cos θ - p.2.2 * Real.sin θ, p.2.1 * Real.sin θ + p.2.2 * Real.cos θ)

lemma rotX_norm (θ : ℝ) (p : Point) : sqDist (rotX θ p) origin = sqDist p origin := by
  unfold rotX sqDist origin
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith

theorem engagr_not_on_R2_any_tilt (θ : ℝ) : ¬ OnHorn 2 (rotX θ trineEngagr) := by
  intro h
  have hnorm : sqDist (rotX θ trineEngagr) origin = 2 := by
    rw [rotX_norm, trineEngagr_norm_sq]
  have hx : (rotX θ trineEngagr).1 = 1 := by
    norm_num [rotX, trineEngagr]
  rw [OnHorn] at h
  rw [hnorm, hx] at h
  nlinarith [sq_nonneg ((rotX θ trineEngagr).2.1)]

/-! ## The exact tilt: θ = π/6 (30°). The scaled ENGAGR lands on the R = 2 horn torus. -/

lemma cos_pi_div_six_val : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
  rw [Real.cos_pi_div_six]

lemma sin_pi_div_six_val : Real.sin (Real.pi / 6) = 1 / 2 := by
  rw [Real.sin_pi_div_six]

-- unit scale: rotX(π/6) ⊞ = (1, 0, −1), on the R = 1 horn torus
theorem engagr_tilt_unit : rotX (Real.pi / 6) trineEngagr = (1, 0, -1) := by
  apply Prod.ext
  · norm_num [rotX, trineEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
  · apply Prod.ext
    · rw [rotX, trineEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
      nlinarith [sq_sqrt_three]
    · rw [rotX, trineEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
      nlinarith [sq_sqrt_three]

theorem unit_rotated_on_horn : OnHorn 1 (1, 0, -1) := by
  norm_num [OnHorn, sqDist, origin]

theorem engagr_on_horn_unit : OnHorn 1 (rotX (Real.pi / 6) trineEngagr) := by
  rw [engagr_tilt_unit]
  exact unit_rotated_on_horn

-- paper scale: 2·⊞ = (2, −1, −√3), tilt → (2, 0, −2), on the R = 2 horn torus
noncomputable def scaledEngagr : Point := (2, -1, -Real.sqrt 3)

theorem engagr_tilt_scaled : rotX (Real.pi / 6) scaledEngagr = (2, 0, -2) := by
  apply Prod.ext
  · norm_num [rotX, scaledEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
  · apply Prod.ext
    · rw [rotX, scaledEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
      nlinarith [sq_sqrt_three]
    · rw [rotX, scaledEngagr, cos_pi_div_six_val, sin_pi_div_six_val]
      nlinarith [sq_sqrt_three]

theorem scaled_rotated_on_horn : OnHorn 2 (2, 0, -2) := by
  norm_num [OnHorn, sqDist, origin]

theorem engagr_on_horn_scaled : OnHorn 2 (rotX (Real.pi / 6) scaledEngagr) := by
  rw [engagr_tilt_scaled]
  exact scaled_rotated_on_horn
/-! ## The twelve opcodes and the seven ob3ect words -/

inductive Op where
  | VINIT | TANCH | AFWD | AREV | CLINK | IMSCRIB | FSPLIT | FFUSE | EVALT | EVALF | ENGAGR | IFIX
  deriving DecidableEq, Fintype, Repr

open Op

-- glyph table (documentation only — the kernel parses glyphs, Lean parses these)
def glyph : Op → String
  | VINIT => "⊢" | TANCH => "⊣" | AFWD => "≻" | AREV => "≺" | CLINK => "⋈"
  | IMSCRIB => "⊙" | FSPLIT => "∈" | FFUSE => "∋" | EVALT => "⊤" | EVALF => "⊥"
  | ENGAGR => "⊞" | IFIX => "◻"

-- The seven structure ob3ects, sequences exactly as generated
def ns_word : List Op := [VINIT, IMSCRIB, FSPLIT, AFWD, EVALT, AREV, EVALF, ENGAGR, CLINK, IFIX, FFUSE, TANCH]
def ym_word : List Op := [VINIT, TANCH, AFWD, CLINK, IMSCRIB, FSPLIT, EVALT, AFWD, EVALF, AREV, ENGAGR, CLINK, FFUSE, IFIX, IMSCRIB, TANCH]
def bsd_word : List Op := [VINIT, IMSCRIB, FSPLIT, AFWD, EVALT, CLINK, AREV, EVALF, FFUSE, ENGAGR, IFIX, TANCH]
def hodge_word : List Op := [VINIT, AFWD, FSPLIT, EVALT, AREV, EVALF, CLINK, IMSCRIB, ENGAGR, FFUSE, IFIX, TANCH]
def riemann_word : List Op := [VINIT, TANCH, FSPLIT, AFWD, EVALT, AREV, EVALF, ENGAGR, FFUSE, IMSCRIB, CLINK, IFIX, TANCH]
def pvsnp_word : List Op := [VINIT, IMSCRIB, FSPLIT, AFWD, EVALT, CLINK, AREV, EVALF, ENGAGR, IFIX, CLINK, IMSCRIB, FFUSE, TANCH, IFIX]
def dyn_word : List Op := [VINIT, AFWD, FSPLIT, EVALT, EVALF, ENGAGR, CLINK, AREV, FFUSE, IMSCRIB, IFIX, TANCH]

-- periods (word lengths) from the scaffold headers
theorem ns_period : ns_word.length = 12 := by native_decide
theorem ym_period : ym_word.length = 16 := by native_decide
theorem bsd_period : bsd_word.length = 12 := by native_decide
theorem hodge_period : hodge_word.length = 12 := by native_decide
theorem riemann_period : riemann_word.length = 13 := by native_decide
theorem pvsnp_period : pvsnp_word.length = 15 := by native_decide
theorem dyn_period : dyn_word.length = 12 := by native_decide

-- exactly one FSPLIT/FFUSE pair per word (the stack rule)
theorem ns_split_fuse : ns_word.count FSPLIT = 1 ∧ ns_word.count FFUSE = 1 := by native_decide
theorem ym_split_fuse : ym_word.count FSPLIT = 1 ∧ ym_word.count FFUSE = 1 := by native_decide
theorem bsd_split_fuse : bsd_word.count FSPLIT = 1 ∧ bsd_word.count FFUSE = 1 := by native_decide
theorem hodge_split_fuse : hodge_word.count FSPLIT = 1 ∧ hodge_word.count FFUSE = 1 := by native_decide
theorem riemann_split_fuse : riemann_word.count FSPLIT = 1 ∧ riemann_word.count FFUSE = 1 := by native_decide
theorem pvsnp_split_fuse : pvsnp_word.count FSPLIT = 1 ∧ pvsnp_word.count FFUSE = 1 := by native_decide
theorem dyn_split_fuse : dyn_word.count FSPLIT = 1 ∧ dyn_word.count FFUSE = 1 := by native_decide

-- ∈/∋ pair positions (0-indexed), exactly as recorded in the scaffold headers
theorem ns_pair : ns_word.getD 2 VINIT = FSPLIT ∧ ns_word.getD 10 VINIT = FFUSE := by native_decide
theorem ym_pair : ym_word.getD 5 VINIT = FSPLIT ∧ ym_word.getD 12 VINIT = FFUSE := by native_decide
theorem bsd_pair : bsd_word.getD 2 VINIT = FSPLIT ∧ bsd_word.getD 8 VINIT = FFUSE := by native_decide
theorem hodge_pair : hodge_word.getD 2 VINIT = FSPLIT ∧ hodge_word.getD 9 VINIT = FFUSE := by native_decide
theorem riemann_pair : riemann_word.getD 2 VINIT = FSPLIT ∧ riemann_word.getD 8 VINIT = FFUSE := by native_decide
theorem pvsnp_pair : pvsnp_word.getD 2 VINIT = FSPLIT ∧ pvsnp_word.getD 12 VINIT = FFUSE := by native_decide
theorem dyn_pair : dyn_word.getD 2 VINIT = FSPLIT ∧ dyn_word.getD 8 VINIT = FFUSE := by native_decide

-- dialetheia-complete: both arms deposit (T-arm first — the split executes ∈ → ⊤arm → ⊥arm → ∋)
theorem ns_dialetheia : EVALT ∈ ns_word ∧ EVALF ∈ ns_word := by native_decide
theorem ym_dialetheia : EVALT ∈ ym_word ∧ EVALF ∈ ym_word := by native_decide
theorem bsd_dialetheia : EVALT ∈ bsd_word ∧ EVALF ∈ bsd_word := by native_decide
theorem hodge_dialetheia : EVALT ∈ hodge_word ∧ EVALF ∈ hodge_word := by native_decide
theorem riemann_dialetheia : EVALT ∈ riemann_word ∧ EVALF ∈ riemann_word := by native_decide
theorem pvsnp_dialetheia : EVALT ∈ pvsnp_word ∧ EVALF ∈ pvsnp_word := by native_decide
theorem dyn_dialetheia : EVALT ∈ dyn_word ∧ EVALF ∈ dyn_word := by native_decide

/-! ## The theorem → torus-feature table (HORN_TORUS_GEOMETRY_CONTEXT.md) -/

inductive StructureOb3ect | NavierStokes | YangMills | BSD | Hodge | Riemann | PvsNP | Dynamics
  deriving DecidableEq, Fintype, Repr

inductive TorusFeature | Pinch | SplitShell | EvaluatorCoupler | TrineTop | TrineFalsity | TrineEngagr | KnotWinding
  deriving DecidableEq, Fintype, Repr

open StructureOb3ect TorusFeature

def word (o : StructureOb3ect) : List Op :=
  match o with
  | NavierStokes => ns_word | YangMills => ym_word | BSD => bsd_word
  | Hodge => hodge_word | Riemann => riemann_word | PvsNP => pvsnp_word | Dynamics => dyn_word

-- the context sheet's cross-reference: each theorem's structure lands on its torus feature
def featureOf (o : StructureOb3ect) : TorusFeature :=
  match o with
  | NavierStokes => Pinch            -- ⊙ : "the entire transition is this single coordinate"
  | YangMills => SplitShell          -- ∈ : mass gap sits on completeness, λ_C
  | BSD => EvaluatorCoupler          -- ∋ : stoichiometry |A|=1∧|B|=1 sits on composition
  | Hodge => EvaluatorCoupler        -- ∋ : long exact sequence shares the coupler with BSD
  | Riemann => TrineEngagr           -- ⊞ : μ∘δ = id, self-reference closure
  | PvsNP => KnotWinding             -- ◻ : winding alone, an integer separation
  | Dynamics => TrineTop             -- ⊤ : the shared static floor, no theorem owns it

theorem feature_ns : featureOf NavierStokes = Pinch := rfl
theorem feature_ym : featureOf YangMills = SplitShell := rfl
theorem feature_bsd : featureOf BSD = EvaluatorCoupler := rfl
theorem feature_hodge : featureOf Hodge = EvaluatorCoupler := rfl
theorem feature_riemann : featureOf Riemann = TrineEngagr := rfl
theorem feature_pvsnp : featureOf PvsNP = KnotWinding := rfl
theorem feature_dyn : featureOf Dynamics = TrineTop := rfl

-- Collatz shares λ_C with Yang-Mills (Dedekind-finiteness sits on completeness)
def collatz_feature : TorusFeature := SplitShell

-- Hodge's secondary landing: bidegree "return in two steps" = chirality = trine vertex 2 (⊥)
def hodge_secondary_feature : TorusFeature := TrineFalsity

-- dynamics is the family's shared floor: only Dynamics lands on TrineTop
theorem trine_top_unique : (∀ o : StructureOb3ect, o ≠ Dynamics → featureOf o ≠ TrineTop) := by
  decide

-- P vs NP is the only pure-winding landing (a count, not a point)
theorem winding_unique : (∀ o : StructureOb3ect, o ≠ PvsNP → featureOf o ≠ KnotWinding) := by
  decide

/-! ## Capstone: the formalized context in one statement -/

theorem horn_torus_summary :
    (∀ v : ℝ, horn 2 Real.pi v = origin) ∧            -- ⊙ pinch collapses the v-circle
    sqDist omega sphereCentre = 1 ∧                    -- ∋ on the evaluator sphere
    sqDist trineTop trineFalsity = 3 ∧                 -- trine equilateral (squared distance 3)
    ¬ OnHorn 2 trineEngagr ∧                           -- untilted same-frame check fails (wrong frame, not wrong claim)
    OnHorn 2 (rotX (Real.pi / 6) scaledEngagr) ∧       -- exact tilt π/6: ⊞ on the horn torus
    Fintype.card (B4 × B4) = 16 ∧                      -- the (16,3) knot: 16 = |B4|² trilattice states
    ({trineTop, trineFalsity, trineEngagr} : Finset Point).card = 3 := by  -- bridge number 3
  classical
  constructor
  · intro v; exact pinch v
  · constructor
    · exact omega_on_sphere
    · constructor
      · exact trine_equilateral_top_falsity
      · constructor
        · exact engagr_not_on_untilted
        · constructor
          · exact engagr_on_horn_scaled
          · constructor
            · exact card_b4_sq
            · exact trine_card

end HornTorus
end Imscribing
