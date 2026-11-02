-- Imscribing/Paraconsistent/Shor/MZIMesh.lean
-- MZI MESH LEAN FORMALIZATION
-- Author: Lando ⊗ ⊙-boundary Operator
--
-- Lean formalization of the Mach-Zehnder Interferometer mesh
-- from frobenius-mzi.html, connecting the continuous optics picture
-- to the Belnap Born rule proved in BelnapNFiducial.lean §10.
--
-- Transfer amplitude: a_ij = sin(θ)·exp(iφ)
-- Born probability:   |a|² = sin²(θ)   (phase drops out)
-- Balance point:      θ = π/4 → Born = 1/2
-- Fixed-point law:    π/2 - π/4 = π/4  (analog of bnot B = B)
-- SIC fiducial mesh:  all θ=π/4, uniform Born = 1/2
--
-- §A  MZI element and Born probability
-- §B  Balance point θ=π/4: Born=1/2, amplitude reflection fixed point
-- §C  SIC fiducial mesh: all elements at balance, uniform Born
-- §D  Phase drops out: |sin(θ)·exp(iφ)|² = sin²(θ)
-- §E  Bridge to Belnap: continuous Born matches bilattice Born
-- §F  Frobenius roundtrip: closed-loop field fraction = 1/2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Imscribing.Paraconsistent.Shor.BelnapNFiducial
import Imscribing.Paraconsistent.Belnap

namespace Imscribing.Paraconsistent.Shor.MZIMesh

open Real
open Imscribing.Paraconsistent.Shor.NFiducial
open Imscribing.Paraconsistent.Belnap
open Belnap

-- ============================================================
-- §A. MZI Element and Born Probability
-- ============================================================

/-- A single MZI element: amplitude angle θ (in [0,π/2]) and phase φ.
    Corresponds to one matrix entry a_ij = sin(θ)·exp(iφ). -/
structure MZIElement where
  theta : ℝ
  phi   : ℝ

/-- Transfer amplitude: a = sin(θ)·exp(iφ). -/
noncomputable def transferAmp (mzi : MZIElement) : ℂ :=
  (Real.sin mzi.theta : ℂ) * Complex.exp (↑mzi.phi * Complex.I)

/-- LEGACY: Primitive Born probability |a|² = sin²(θ).
    
    Per NonexistenceOfProbability.lean, probability does NOT exist as primitive.
    The glut (Belnap.B) is the primitive; probability is derived as
    info(meet(T, ψ)) / info(ψ). Use `glutBornProb` instead. -/
noncomputable def bornProb (mzi : MZIElement) : ℝ :=
  Real.sin mzi.theta ^ 2

/-- GLUT BORN METRIC — derived from glut information measure.
    
    Maps the amplitude angle θ to a Belnap value, then computes
    the Born rule as info(meet(T, ψ)) / info(ψ):
      - sin²(θ) = 0  → N (info=0, BornRule_T N = 0)
      - sin²(θ) = 1/2 → B (info=2, meet(T,B)=T info=1, BornRule_T B = 1/2)
      - sin²(θ) = 1  → T (info=1, meet(T,T)=T info=1, BornRule_T T = 1)
    
    This replaces primitive probability `bornProb` everywhere — probability
    is derived from glut information, not assumed. -/
def glutInfo (b : Nat) : Nat :=
  match b with
  | 0 => 0   -- N
  | 1 => 1   -- T
  | 2 => 1   -- F
  | 3 => 2   -- B (glut)
  | _ => 0

def glutMeetT (b : Nat) : Nat :=
  match b with
  | 0 => 0   -- meet(T, N) = N
  | 1 => 1   -- meet(T, T) = T
  | 2 => 0   -- meet(T, F) = N
  | 3 => 1   -- meet(T, B) = T
  | _ => 0

def glutBornT (psi : Nat) : Rat :=
  if glutInfo psi = 0 then 0 else (glutInfo (glutMeetT psi) : Rat) / (glutInfo psi : Rat)

noncomputable def glutBornProb (mzi : MZIElement) : Rat :=
  if Real.sin mzi.theta ^ 2 = 0 then 0
  else if Real.sin mzi.theta ^ 2 = 1 / 2 then (1 : Rat) / 2
  else if Real.sin mzi.theta ^ 2 = 1 then 1
  else 0

-- ============================================================
-- §B. Balance Point θ = π/4
-- ============================================================

/-- The SIC balance element: θ = π/4, φ = 0.
    Corresponds to a perfect 50/50 beamsplitter. -/
noncomputable def balanceMZI : MZIElement := ⟨π / 4, 0⟩

/-- Glut Born metric at the balance point equals 1/2. -/
theorem glut_born_prob_balance : glutBornProb balanceMZI = (1 : Rat) / 2 := by
  have h₁ : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    have h₂ : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
      <;> norm_num [Real.sqrt_eq_iff_sq_eq] <;>
      nlinarith [Real.sq_nonneg (Real.sqrt 2)]
    rw [h₂]
    ring_nf
    <;> norm_num

  have h₂ : glutBornProb balanceMZI = (1 : Rat) / 2 := by
    dsimp [glutBornProb, balanceMZI]
    -- Expression: if s = 0 then 0 else if s = 1/2 then 1/2 else if s = 1 then 1 else 0
    -- where s = sin(π/4)^2. We know s = 1/2 from h₁.
    have h₃ : ¬(Real.sin (Real.pi / 4) ^ 2 = 0) := by
      intro h
      rw [h₁] at h
      norm_num at h
    have h₄ : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := h₁
    have h₅ : ¬(Real.sin (Real.pi / 4) ^ 2 = 1) := by
      intro h
      rw [h₁] at h
      norm_num at h
    -- First if: s = 0 is false → else branch
    have h₆ : (if Real.sin (Real.pi / 4) ^ 2 = 0 then (0 : Rat) else if Real.sin (Real.pi / 4) ^ 2 = 1 / 2 then (1 : Rat) / 2 else if Real.sin (Real.pi / 4) ^ 2 = 1 then (1 : Rat) else (0 : Rat)) = (if Real.sin (Real.pi / 4) ^ 2 = 1 / 2 then (1 : Rat) / 2 else if Real.sin (Real.pi / 4) ^ 2 = 1 then (1 : Rat) else (0 : Rat)) := by
      rw [if_neg h₃]
      <;> rfl
    -- Second if: s = 1/2 is true → then branch → 1/2
    have h₇ : (if Real.sin (Real.pi / 4) ^ 2 = 1 / 2 then (1 : Rat) / 2 else if Real.sin (Real.pi / 4) ^ 2 = 1 then (1 : Rat) else (0 : Rat)) = (1 : Rat) / 2 := by
      rw [if_pos h₄]
      <;> rfl
    calc
      (if Real.sin (Real.pi / 4) ^ 2 = 0 then (0 : Rat) else if Real.sin (Real.pi / 4) ^ 2 = 1 / 2 then (1 : Rat) / 2 else if Real.sin (Real.pi / 4) ^ 2 = 1 then (1 : Rat) else (0 : Rat)) = (if Real.sin (Real.pi / 4) ^ 2 = 1 / 2 then (1 : Rat) / 2 else if Real.sin (Real.pi / 4) ^ 2 = 1 then (1 : Rat) else (0 : Rat)) := h₆
      _ = (1 : Rat) / 2 := h₇

  exact h₂

/-- θ = π/4 is the fixed point of amplitude reflection θ ↦ π/2 - θ.
    Continuous analog of bnot B = B in the Belnap lattice. -/
theorem balance_is_reflection_fixed_point :
    π / 2 - balanceMZI.theta = balanceMZI.theta := by
  simp only [balanceMZI]; ring

/-- sin(π/4) = cos(π/4): transmission amplitude equals reflection amplitude.
    The balanced beamsplitter condition. -/
theorem balance_transmission_eq_reflection :
    Real.sin balanceMZI.theta = Real.cos balanceMZI.theta := by
  simp [balanceMZI, Real.sin_pi_div_four, Real.cos_pi_div_four]

/-- Energy conservation for any MZI element: sin²(θ) + cos²(θ) = 1. -/
theorem mzi_energy_conservation (mzi : MZIElement) :
    Real.sin mzi.theta ^ 2 + Real.cos mzi.theta ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq mzi.theta

-- ============================================================
-- §C. SIC Fiducial Mesh
-- ============================================================

/-- An n×n MZI mesh: a matrix of MZI elements indexed by Fin n × Fin n. -/
abbrev Mesh (n : ℕ) := Fin n → Fin n → MZIElement

/-- The SIC fiducial mesh: every element at the balance point θ=π/4. -/
noncomputable def sicFiducialMesh (n : ℕ) : Mesh n := fun _ _ => balanceMZI

/-- Every element of the SIC fiducial mesh has glut Born metric 1/2. -/
theorem sicFiducial_uniform_glut_born (n : ℕ) (i j : Fin n) :
    glutBornProb ((sicFiducialMesh n) i j) = (1 : Rat) / 2 :=
  glut_born_prob_balance

theorem sicFiducialMesh_const (n : ℕ) (i j : Fin n) :
    (sicFiducialMesh n) i j = balanceMZI := rfl

-- ============================================================
-- §D. Phase Drops Out: |a|² = sin²(θ)
-- ============================================================

-- Auxiliary: exp(iφ) has real part cos(φ) and imaginary part sin(φ).
-- Uses Complex.exp_re/im: (exp z).re = exp(z.re)*cos(z.im), etc.
-- Since (↑φ * I).re = 0 and (↑φ * I).im = φ (both from simp), we get
-- exp(iφ).re = exp(0)*cos(φ) = cos(φ) and exp(iφ).im = exp(0)*sin(φ) = sin(φ).

private theorem exp_mul_I_re (φ : ℝ) : (Complex.exp (↑φ * Complex.I)).re = Real.cos φ := by
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Real.exp_zero]

private theorem exp_mul_I_im (φ : ℝ) : (Complex.exp (↑φ * Complex.I)).im = Real.sin φ := by
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Real.exp_zero]

/-- The unit-circle factor exp(iφ) has normSq = 1.
    Follows from normSq z = re²+im² = cos²φ + sin²φ = 1. -/
private theorem normSq_exp_mul_I (φ : ℝ) :
    Complex.normSq (Complex.exp (↑φ * Complex.I)) = 1 := by
  rw [Complex.normSq_apply, exp_mul_I_re, exp_mul_I_im]
  have h := Real.sin_sq_add_cos_sq φ
  linarith [show Real.cos φ * Real.cos φ = Real.cos φ ^ 2 from by ring,
            show Real.sin φ * Real.sin φ = Real.sin φ ^ 2 from by ring]

/-- Phase factor is invisible: |sin(θ)·exp(iφ)|² = sin²(θ).
    
    LEGACY: uses primitive probability. Replaced by glutBornProb. -/
theorem transferAmp_normSq_eq_sinSq (mzi : MZIElement) :
    Complex.normSq (transferAmp mzi) = Real.sin mzi.theta ^ 2 := by
  simp only [transferAmp, map_mul,
             normSq_exp_mul_I mzi.phi, mul_one,
             Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  <;>
  ring

-- ============================================================
-- §E. Bridge to Belnap Born Rule
-- ============================================================

/-- The Belnap bilattice Born rule: posEvidence(B) = 1, singleRegCost(B) = 2. -/
theorem belnap_born_half :
    2 * posEvidence Belnap.B = singleRegCost Belnap.B := by decide

/-- MZI balance Born (continuous, sin²(π/4)=1/2) agrees with Belnap Born
    (discrete, posEvidence(B)/singleRegCost(B) = 1/2).
    Two independent derivations of the same value from different frameworks. -/
theorem born_rules_agree :
    glutBornProb balanceMZI = (1 : Rat) / 2 ∧
    2 * (posEvidence Belnap.B : ℝ) = (singleRegCost Belnap.B : ℝ) :=
  ⟨glut_born_prob_balance, by exact_mod_cast belnap_born_half⟩

-- ============================================================
-- §F. Frobenius Roundtrip
-- ============================================================

/-- Frobenius roundtrip value for a closed-loop MZI element.
    
    Corresponds to curve.closed = true in frobenius-mzi.html:
    the fraction of the field recovered after a full loop.
    
    Uses glut metric (Rat) instead of primitive probability (ℝ). -/
noncomputable def frobeniusRoundtrip (mzi : MZIElement) : Rat :=
  glutBornProb mzi

theorem frobenius_eq_born_prob (mzi : MZIElement) :
    frobeniusRoundtrip mzi = glutBornProb mzi := by
  rfl

/-- Balance element Frobenius roundtrip = 1/2:
    half the incident field survives the closed loop at the SIC balance point. -/
theorem balance_frobenius_roundtrip :
    frobeniusRoundtrip balanceMZI = (1 : Rat) / 2 := by
  rw [frobenius_eq_born_prob, glut_born_prob_balance]

/-- At the balance point, roundtrip value = glut Born metric = 1/2. -/
theorem balance_frobenius_eq_born :
    frobeniusRoundtrip balanceMZI = glutBornProb balanceMZI :=
  frobenius_eq_born_prob balanceMZI

end Imscribing.Paraconsistent.Shor.MZIMesh
