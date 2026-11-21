/-
CanonicalWitness.lean — §46W. Canonical observable non-constancy for the
strong-coupling infinite-volume bridge.

Direct, self-contained witness built from:
- `suFlip2` / `suFlip2_trace_re` / `su_one_trace_re` (CubicHaar4D)
- the explicit four-link embedding of `canonicalLoop4DZ`
- the unit-step non-degeneracy lemmas `intCastFin_succ_ne` / `projSite4_stepS_ne`
  already proved in ContinuumClosure
-/
import Mathlib
import Imscribing.YangMills.ContinuumClosure

namespace YangMills

open Complex Real

variable (N : ℕ) (hN : 2 ≤ N)
  [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
  [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]

/-! ## §46W.1  Unfolding the embedded canonical plaquette loop -/

/-- The canonical plaquette loop at `x` as an explicit link list on
`cubicTorus4 L L`.  (Identical to the ContinuumClosure statement; re-exported
for a self-contained witness file.) -/
theorem embedLoop4DZ_canonicalPlaq (L : ℕ) [NeZero L] (x : Space4) :
    embedLoop4DZ L (canonicalLoop4DZ x) =
      [ ((projSite4 L (fun i => ⌊x i⌋), 1), true),
        ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), 2), true),
        ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
          (1, false)), 1), false),
        ((projSite4 L (fun i => ⌊x i⌋), 2), false) ] := by
  -- The ContinuumClosure version writes the fourth site after the final
  -- compensating step; that site is identically the base.
  have hW := embedLoop4DZ_canonicalPlaqW L x
  have hlast :
      stepZ4 (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
        (1, false)) (2, false) = (fun i => ⌊x i⌋) := by
    dsimp [stepZ4]
    funext i; fin_cases i <;> simp [stepZ4] <;> split_ifs <;> ring
  -- Both lists begin with the same three links; the fourth links coincide
  -- after rewriting the site by hlast.
  simpa [hlast] using hW

/-! ## §46W.2  Witness fields -/

/-- Trivial witness field. -/
def witnessFieldOne (L : ℕ) [NeZero L] :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun _ => 1

/-- Single-flip witness field: exactly the base-site direction-1 link of the
canonical plaquette carries `suFlip2`; every other link is trivial. -/
def witnessFieldFlip (L : ℕ) [NeZero L] (x : Space4) :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun e =>
  if e = ((projSite4 L (fun i => ⌊x i⌋), 1) : (cubicTorus4 L L).Link) then suFlip2 N hN else 1

theorem witnessFieldOne_hol (L : ℕ) [NeZero L] (x : Space4) :
    pathHolonomy (witnessFieldOne L)
      (embedLoop4DZ L (canonicalLoop4DZ x)) = 1 := by
  have h_fwd : ∀ γ : List ((cubicTorus4 L L).Link × Bool),
      pathHolonomy (witnessFieldOne L) γ = 1 := by
    intro γ
    induction γ with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      have hU : witnessFieldOne L e = 1 := rfl
      cases b
      · simp only [pathHolonomy, List.cons, hU, inv_one, ih]
      · simp only [pathHolonomy, List.cons, hU, one_mul, ih]
  exact h_fwd _

/-- The three tail links of the embedded canonical plaquette differ from the
base-site direction-1 link. -/
theorem tail_links_ne_base (L : ℕ) [NeZero L] (hL : 2 ≤ L) (x : Space4) :
    ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), 2) : (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), 1) : (cubicTorus4 L L).Link) ∧
    ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
      (1, false)), 1) : (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), 1) : (cubicTorus4 L L).Link) ∧
    ((projSite4 L (fun i => ⌊x i⌋), 2) : (cubicTorus4 L L).Link) ≠
      ((projSite4 L (fun i => ⌊x i⌋), 1) : (cubicTorus4 L L).Link) := by
  refine ⟨?_, ?_, ?_⟩
  · -- directions 2 ≠ 1
    intro h
    exact absurd (congrArg Prod.snd h) (by decide : (2 : Fin 4) ≠ 1)
  · -- sites differ by a unit step in coordinate 2
    have hstep :
        stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true)) (1, false) =
          stepZ4 (fun i => ⌊x i⌋) (2, true) := by
      dsimp [stepZ4]
      funext i; fin_cases i <;> simp [stepZ4] <;> split_ifs <;> rfl
    intro h
    rw [hstep] at h
    exact projSite4_stepS_ne L hL (fun i => ⌊x i⌋) (2 : Fin 4) true (congrArg Prod.fst h)
  · -- directions 2 ≠ 1
    intro h
    exact absurd (congrArg Prod.snd h) (by decide : (2 : Fin 4) ≠ 1)

theorem witnessFieldFlip_hol (L : ℕ) [NeZero L] (hL : 2 ≤ L) (x : Space4) :
    pathHolonomy (witnessFieldFlip L hN x)
      (embedLoop4DZ L (canonicalLoop4DZ x)) = suFlip2 N hN := by
  rw [embedLoop4DZ_canonicalPlaq]
  have h1 : witnessFieldFlip L hN x
      ((projSite4 L (fun i => ⌊x i⌋), 1) : (cubicTorus4 L L).Link) = suFlip2 N hN := if_pos rfl
  have h2 : witnessFieldFlip L hN x
      ((projSite4 L (stepZ4 (fun i => ⌊x i⌋) (1, true)), 2) : (cubicTorus4 L L).Link) = 1 :=
    if_neg (tail_links_ne_base N hN L hL x).1
  have h3 : witnessFieldFlip L hN x
      ((projSite4 L (stepZ4 (stepZ4 (stepZ4 (fun i => ⌊x i⌋) (1, true)) (2, true))
        (1, false)), 1) : (cubicTorus4 L L).Link) = 1 :=
    if_neg (tail_links_ne_base N hN L hL x).2.1
  have h4 : witnessFieldFlip L hN x
      ((projSite4 L (fun i => ⌊x i⌋), 2) : (cubicTorus4 L L).Link) = 1 :=
    if_neg (tail_links_ne_base N hN L hL x).2.2
  simp only [pathHolonomy, List.cons, h1, h2, h3, h4]
  norm_num [inv_one, mul_one]

/-! ## §46W.3  Non-constancy of the canonical observable -/

/-- **Non-constancy of the canonical single-point plaquette observable.**
For every `L ≥ 2` and every spacetime point `x`, the normalized Wilson loop
of the elementary plaquette takes two distinct values:
- value `1` on the trivial field,
- value `(N-4)/N` on the single-flip field. -/
theorem canonicalWildcard_nonconst (L : ℕ) [NeZero L] (hL : 2 ≤ L) (x : Space4) :
    ∃ U₁ U₂ : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ),
      normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) U₁ ≠
        normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) U₂ := by
  refine ⟨witnessFieldOne L, witnessFieldFlip L hN x, ?_⟩
  have hv1 : normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) (witnessFieldOne L) = 1 := by
    dsimp [normWilsonLoop4]
    rw [witnessFieldOne_hol]
    -- (trace 1).re = N  ⇒  (1/N)·N = 1
    have htr := su_one_trace_re N
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp [htr]
  have hv2 : normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x))
      (witnessFieldFlip L hN x) = ((N : ℝ)⁻¹ * (N - 4 : ℝ) : ℂ) := by
    dsimp [normWilsonLoop4]
    rw [witnessFieldFlip_hol N hN L hL x, suFlip2_trace_re N hN]
    simp
  intro hne
  rw [hv1, hv2] at hne
  -- clearing the common factor 1/N yields N = N-4, absurd for N ≥ 2
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hh : (N : ℝ)⁻¹ * (N - 4 : ℝ) = 1 := by
    simpa [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_inv] using hne
  field_simp [hNne] at hh
  linarith

end YangMills

-- Realization audit (should report only standard Mathlib / kernel axioms)
#print axioms YangMills.canonicalWildcard_nonconst
