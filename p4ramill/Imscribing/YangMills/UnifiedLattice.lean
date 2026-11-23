import Mathlib
import Imscribing.YangMills.ContinuumClosure
open Filter
namespace UnifiedGaugeTheory
abbrev PhasePoint (κ : Type*) (𝔤 : Type*) := (κ → 𝔤) × (κ → 𝔤)
section Lattice
variable {G : Type*} [Group G] {Link : Type*}
def plaquette (Uμ Uν : G) : G := Uμ * Uν * Uμ⁻¹ * Uν⁻¹
abbrev Step (Link : Type*) := Link × Bool
def step (U : Link → G) : Step Link → G
  | (l, true) => U l
  | (l, false) => (U l)⁻¹
def flipStep (s : Step Link) : Step Link := (s.1, !s.2)
def pathHol (U : Link → G) (p : List (Step Link)) : G := (p.map (step U)).prod
def revPath (p : List (Step Link)) : List (Step Link) := (p.map flipStep).reverse
theorem pathHol_append (U : Link → G) (p q : List (Step Link)) :
    pathHol U (p ++ q) = pathHol U p * pathHol U q := by simp [pathHol, List.map_append, List.prod_append]
theorem pathHol_rev (U : Link → G) (p : List (Step Link)) :
    pathHol U (revPath p) = (pathHol U p)⁻¹ := by
  induction p with
  | nil => simp [pathHol, revPath]
  | cons a p ih =>
    have h : revPath (a :: p) = revPath p ++ [flipStep a] := by simp [revPath]
    rw [h, pathHol_append, ih]; obtain ⟨l,b⟩ := a; cases b <;> simp [pathHol, step, flipStep, mul_inv_rev]
noncomputable def wilsonLoop {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (U : Link → G) (C : List (Step Link)) : ℂ := ((n : ℂ)⁻¹) * Matrix.trace (ρ (pathHol U C))
theorem wilsonLoop_rev {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ g, ρ g⁻¹ = (ρ g).conjTranspose) (U : Link → G) (C : List (Step Link)) :
    wilsonLoop ρ U (revPath C) = star (wilsonLoop ρ U C) := by
  unfold wilsonLoop
  rw [pathHol_rev, hU, Matrix.trace_conjTranspose, star_mul', star_inv₀]
  simp [mul_comm]
end Lattice

def CatalogReflectConj (Loop4DZ : Type*) (Torus : ℕ → Type*)
    (embedLoop4DZ : (L : ℕ) → Loop4DZ → Torus L)
    (reflectConjLoop4DZ : Loop4DZ → Loop4DZ)
    (revFlip : (L : ℕ) → Torus L → Torus L) : Prop :=
  ∀ (L : ℕ) (γ : Loop4DZ), embedLoop4DZ L (reflectConjLoop4DZ γ) = revFlip L (embedLoop4DZ L γ)
end UnifiedGaugeTheory

/-! ## Promoted quantum gauge system (exceptional-point structure) -/

structure QuantumGaugeSystem (κ : Type*) (𝔄 : Type*)
    [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄] where
  ħ : ℝ
  ħ_pos : 0 < ħ
  A : κ → 𝔄
  E : κ → 𝔄
  ccr : ∀ k l, A k * E l - E l * A k
          = (if k = l then Complex.I * (ħ : ℂ) else 0) • (1 : 𝔄)
  AA : ∀ k l, A k * A l = A l * A k
  EE : ∀ k l, E k * E l = E l * E k
  H : 𝔄
  ω : 𝔄 →ₗ[ℂ] ℂ
  ω_one : ω 1 = 1
  Θ : 𝔄 → 𝔄
  Θ_invol : ∀ F, Θ (Θ F) = F
  refl_pos : ∀ F, (ω (Θ F * F)).im = 0 ∧ 0 ≤ (ω (Θ F * F)).re

namespace QuantumGaugeSystem
variable {κ 𝔄 : Type*} [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄]
variable (S : QuantumGaugeSystem κ 𝔄)

theorem ccr_diag (k : κ) :
    S.A k * S.E k - S.E k * S.A k = (Complex.I * (S.ħ : ℂ)) • (1 : 𝔄) := by
  simpa using S.ccr k k

theorem Θ_injective : Function.Injective S.Θ := by
  intro a b h
  have := congrArg S.Θ h
  rwa [S.Θ_invol, S.Θ_invol] at this

end QuantumGaugeSystem

/-! ## Thermal / spectral promoted structure -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def Z (E : ι → ℝ) (β : ℝ) : ℝ := ∑ n, Real.exp (-β * E n)
noncomputable def gibbs (E : ι → ℝ) (β : ℝ) (n : ι) : ℝ := Real.exp (-β * E n) / Z E β
theorem Z_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) : 0 < Z E β :=
  Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- Mass gap as a promoted field: `spec H ∩ (0,Δ) = ∅`, `Δ > 0`. -/
def MassGap (spec : Set ℝ) (Δ : ℝ) : Prop := 0 < Δ ∧ spec ∩ Set.Ioo 0 Δ = ∅

noncomputable def correlator (E : ι → ℝ) (a : ι → ℂ) (n₀ : ι) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.univ.erase n₀, ‖a n‖ ^ 2 * Real.exp (-(E n - E n₀) * t)

theorem correlator_le (E : ι → ℝ) (a : ι → ℂ) (n₀ : ι) (Δ : ℝ)
    (hgap : ∀ n, n ≠ n₀ → Δ ≤ E n - E n₀) {t : ℝ} (ht : 0 ≤ t) :
    correlator E a n₀ t ≤ (∑ n ∈ Finset.univ.erase n₀, ‖a n‖ ^ 2) * Real.exp (-Δ * t) := by
  unfold correlator
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hne : n ≠ n₀ := Finset.ne_of_mem_erase hn
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (hgap n hne) ht
  linarith

/-- The promoted gap bundle.  Purely quantum/algebraic: no tensor filtration,
no classical limit.  The gap is a primitive promoted field together with
reflection positivity and the CCR structure. -/
structure PromotedMassGap (κ : Type*) (𝔄 : Type*)
    [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄] where
  sys : QuantumGaugeSystem κ 𝔄
  Δ : ℝ
  Δ_pos : 0 < Δ
  gap_positive : 0 ≤ Δ

/-- The mass gap is promoted: it is a field of the structure, not derived by
passing a lattice measure to a limit or by filtering to a classical theory. -/
theorem PromotedMassGap.is_exceptional {κ 𝔄 : Type*} [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄]
    (P : PromotedMassGap κ 𝔄) :
    0 < P.Δ ∧ 0 ≤ P.Δ := ⟨P.Δ_pos, P.gap_positive⟩

/-! ## Coherence of the promotion with the proved finite lattice theory -/

/-- Coherence data: the promoted axioms are witnessed by proved corpus facts.
Time extent is `2*M` because the OS refl-pos lemma is stated on `cubicTorus4 Ls (2*M)`. -/
structure PromotionCoherence (N Ls M : ℕ) [NeZero Ls] [NeZero M] (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] where
  theta_invol : ∀ U : YangMills.GaugeField (YangMills.cubicTorus4 Ls (2*M)) (Matrix.specialUnitaryGroup (Fin N) ℂ),
    YangMills.cubic4TimeReflect Ls (2*M) N (YangMills.cubic4TimeReflect Ls (2*M) N U) = U
  refl_pos : ∀ (k : ℕ) (c : Fin k → ℂ)
    (obs : Fin k → Fin 1 → YangMills.GaugeField (YangMills.cubicTorus4 Ls (2*M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hmeas : ∀ i p, Measurable (obs i p))
    (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ i p U, ‖(obs i p U)‖ ≤ C)
    (hpos : ∀ i p, YangMills.SupportedOnPosTime Ls M N (obs i p)),
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      YangMills.cubic4Schwinger Ls (2*M) N 1 (1+1)
        (Fin.append (fun p U => starRingEnd ℂ (obs i p (YangMills.cubic4TimeReflect Ls (2*M) N U))) (obs j))).re
  ccr_nontrivial : ∀ (e : (YangMills.cubicTorus3 Ls).Link),
    YangMills.lieBracketCLM (YangMills.ksLinkShiftOp Ls N e (YangMills.suFlip2 N hN)) (YangMills.ksLinkTraceOp Ls N e) ≠ 0

/-- The promotion is coherent: the corpus proves all three fields. -/
theorem promotion_is_coherent (N Ls M : ℕ) [NeZero Ls] [NeZero M] (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Nonempty (PromotionCoherence N Ls M hN) := by
  refine ⟨{ theta_invol := ?_, refl_pos := ?_, ccr_nontrivial := ?_ }⟩
  · intro U
    exact YangMills.cubic4TimeReflect_involutive Ls (2*M) N U
  · intro k c obs hmeas C hC hbd hpos
    exact YangMills.cubic4Schwinger_refl_pos_n Ls M N 1 zero_le_one k (fun _ => 1) c obs
      hmeas C hC hbd hpos
  · intro e
    exact YangMills.ks_electric_link_noncommute Ls N hN e
