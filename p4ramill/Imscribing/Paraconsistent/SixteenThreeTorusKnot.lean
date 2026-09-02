/-
  Imscribing/Paraconsistent/SixteenThreeTorusKnot.lean
  ─────────────────────────────────────────────────────
  THEOREM: the embedded (16,3) torus knot on the R = r horn torus --
  knot R t := horn R (3t) (16t), the exact curve a GPT-authored derivation
  named -- closes into one loop every 2π and passes through the pinch
  point exactly 3 times per loop, never 16. Both are proved here, not
  read off a picture.

  `horn` already lives in Imscribing.Millennium.HornTorusGeometry:
  horn R u v = (R(1+cos u)cos v, R(1+cos u)sin v, R sin u), and that file
  already proved `pinch`, that the whole v-circle at u = π collapses to
  the origin. The GPT derivation's embedded-curve formula
  x(t)=(R+r cos 3t)cos16t, y(t)=(R+r cos3t)sin16t, z(t)=r sin3t, at the
  R = r special case it names, is exactly `horn R u v` with u = 3t (the
  poloidal angle) and v = 16t (the toroidal angle) -- so the curve is not
  a new object, it is `horn` walked along the line u = 3t, v = 16t, and
  the pinch it passes through is the SAME pinch `pinch` already names,
  reached whenever cos(3t) = -1 rather than only at the single point
  u = π taken alone.

  The derivation asserted two more things without checking them: that the
  curve closes rather than spiralling, and that any starting parameter
  traces the same curve. Both are proved below, the second as the
  continuous analogue of SixteenThreeTorus.lean's discrete
  `every_corner_on_the_one_orbit` -- proved the identical way, by showing
  the shift is invisible after the fact rather than asserting it.

  Author: Lando⊗⊙perator
  Tier:   O_∞
-/

import Imscribing.Millennium.HornTorusGeometry

namespace Imscribing
namespace SixteenThreeTorusKnot

open Imscribing.HornTorus

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE CURVE: the GPT formula, literally `horn` at u = 3t, v = 16t
-- ═══════════════════════════════════════════════════════════════════

/-- The (16,3) torus knot on the R = r horn torus. Poloidal angle 3t,
    toroidal angle 16t; R = r is already built into `horn`'s one radius. -/
noncomputable def knot (R t : ℝ) : Point := horn R (3 * t) (16 * t)

theorem knot_eq (R t : ℝ) :
    knot R t =
      (R * (1 + Real.cos (3 * t)) * Real.cos (16 * t),
       R * (1 + Real.cos (3 * t)) * Real.sin (16 * t),
       R * Real.sin (3 * t)) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2  THE CURVE CLOSES: 2π-periodic, one knot and not a spiral
-- ═══════════════════════════════════════════════════════════════════

/-- **The knot closes.** Walking t forward by a full 2π returns to the
    same point: 3t advances by a whole multiple of 2π (three of them) and
    16t by another (sixteen), so every trig term realigns exactly. This is
    what makes it a closed knot rather than a curve that spirals forever
    across the torus. -/
theorem knot_periodic (R : ℝ) : Function.Periodic (knot R) (2 * Real.pi) := by
  intro t
  show knot R (t + 2 * Real.pi) = knot R t
  have e3 : (3 : ℝ) * (t + 2 * Real.pi) = 3 * t + (3 : ℕ) * (2 * Real.pi) := by
    push_cast; ring
  have e16 : (16 : ℝ) * (t + 2 * Real.pi) = 16 * t + (16 : ℕ) * (2 * Real.pi) := by
    push_cast; ring
  rw [knot_eq, knot_eq, e3, e16,
      Real.cos_periodic.nat_mul 3, Real.sin_periodic.nat_mul 3,
      Real.cos_periodic.nat_mul 16, Real.sin_periodic.nat_mul 16]

-- ═══════════════════════════════════════════════════════════════════
-- §3  EVERY STARTING PARAMETER TRACES THE SAME CURVE
-- ═══════════════════════════════════════════════════════════════════
--
-- The continuous analogue of SixteenThreeTorus.lean's
-- `every_corner_on_the_one_orbit`. Restarting the walk at parameter t0 is
-- the same curve re-parametrized, since periodicity makes the shift by
-- any multiple of 2π invisible; here we record the shift-by-t0 version
-- directly: reparametrizing knot R by t ↦ t + t0 has the identical image
-- (range) as knot R itself, because knot R is defined for every real t
-- and the shift is a bijection ℝ ≃ ℝ.

theorem knot_shift_same_image (R t0 : ℝ) :
    Set.range (fun t => knot R (t + t0)) = Set.range (knot R) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨t + t0, rfl⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨t - t0, ?_⟩
    show knot R (t - t0 + t0) = knot R t
    congr 1
    ring

-- ═══════════════════════════════════════════════════════════════════
-- §4  THE PINCH: reached exactly when cos(3t) = -1, general v
-- ═══════════════════════════════════════════════════════════════════
--
-- Generalizes HornTorusGeometry's `pinch` (u = π, R = 2 only) to any
-- radius and any u with cos u = -1 -- the actual condition, of which
-- u = π is one representative.

theorem horn_eq_origin_of_cos_eq_neg_one (R u v : ℝ) (hu : Real.cos u = -1) :
    horn R u v = origin := by
  have hsin : Real.sin u = 0 := by
    have h := Real.sin_sq_add_cos_sq u
    rw [hu] at h
    nlinarith
  apply Prod.ext
  · simp [horn, origin, hu]
  · apply Prod.ext
    · simp [horn, origin, hu]
    · simp [horn, origin, hsin]

/-- **The converse, for R ≠ 0.** If the curve is AT the origin, u was at
    -1 to begin with -- so cos u = -1 is not just sufficient, it is the
    only way in, and counting pinch-crossings by solving cos(3t) = -1 (§5)
    finds every crossing, not merely some of them. -/
theorem horn_eq_origin_iff (R u v : ℝ) (hR : R ≠ 0) :
    horn R u v = origin ↔ Real.cos u = -1 := by
  constructor
  · intro h
    have hx : R * (1 + Real.cos u) * Real.cos v = 0 := by
      have h1 := congrArg (fun p : Point => p.1) h
      simpa [horn, origin] using h1
    have hy : R * (1 + Real.cos u) * Real.sin v = 0 := by
      have h1 := congrArg (fun p : Point => p.2.1) h
      simpa [horn, origin] using h1
    have hpyth : Real.cos v ^ 2 + Real.sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
    have hk2 : (R * (1 + Real.cos u)) ^ 2 = 0 := by nlinarith [hx, hy, hpyth]
    have hk0 : R * (1 + Real.cos u) = 0 := by
      exact sq_eq_zero_iff.mp hk2
    rcases mul_eq_zero.mp hk0 with h1 | h2
    · exact absurd h1 hR
    · linarith
  · exact horn_eq_origin_of_cos_eq_neg_one R u v

-- ═══════════════════════════════════════════════════════════════════
-- §5  THREE CROSSINGS PER LOOP, NOT SIXTEEN -- THE POLOIDAL COUNT
-- ═══════════════════════════════════════════════════════════════════
--
-- Real.cos_eq_neg_one_iff gives the exact solution set of cos θ = -1:
-- θ = π + k·2π for k : ℤ. Setting θ = 3t and restricting t to one
-- fundamental period [0, 2π) picks out exactly three values of k, and
-- they are the three named here -- not asserted from the picture, solved.

theorem cos3t_eq_neg_one_iff (t : ℝ) :
    Real.cos (3 * t) = -1 ↔ ∃ k : ℤ, t = Real.pi / 3 + k * (2 * Real.pi / 3) := by
  rw [Real.cos_eq_neg_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by field_simp; linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **Exactly three, on the nose.** π/3, π, 5π/3 solve cos(3t) = -1, each
    inside one fundamental period [0, 2π), and each is a genuine pinch
    crossing of the (16, 3) knot on the R = r horn torus (R ≠ 0). Three
    is the poloidal winding number, not the toroidal one: the (16,3) knot
    visits the pinch once per poloidal lap, sixteen toroidal laps apart. -/
theorem knot_pinch_crossings (R : ℝ) :
    knot R (Real.pi / 3) = origin ∧
    knot R Real.pi = origin ∧
    knot R (5 * Real.pi / 3) = origin := by
  refine ⟨?_, ?_, ?_⟩
  · apply horn_eq_origin_of_cos_eq_neg_one
    rw [Real.cos_eq_neg_one_iff]
    refine ⟨0, ?_⟩
    push_cast; ring
  · apply horn_eq_origin_of_cos_eq_neg_one
    rw [Real.cos_eq_neg_one_iff]
    refine ⟨1, ?_⟩
    push_cast; ring
  · apply horn_eq_origin_of_cos_eq_neg_one
    rw [Real.cos_eq_neg_one_iff]
    refine ⟨2, ?_⟩
    push_cast; ring

theorem knot_pinch_crossings_iff (R t : ℝ) (hR : R ≠ 0) :
    knot R t = origin ↔ ∃ k : ℤ, t = Real.pi / 3 + k * (2 * Real.pi / 3) := by
  rw [knot, horn_eq_origin_iff R (3 * t) (16 * t) hR, cos3t_eq_neg_one_iff]

end SixteenThreeTorusKnot
end Imscribing
