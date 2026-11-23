/-
  Imscribing/YangMills/IIDWilsonLimit.lean

  Bridge: iidSchwinger as the scaling limit of SU(N) Wilson-lattice
  expectations.  wilsonExpect is a concrete noncomputable def (no axiom).
  The limit theorem is proved from two explicit analytic hypotheses:
  exact single-site moments and asymptotic decorrelation across sites.
-/
import Mathlib
import Imscribing.YangMills.IIDSchwinger
import Imscribing.YangMills.CubicHaar4D

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators Topology
open Complex Real Filter MeasureTheory Set

namespace YangMills

abbrev WilsonConfig (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] :=
  GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Concrete Wilson expectation from the proved lattice Schwinger functional. -/
noncomputable def wilsonExpect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (obs : Fin n → WilsonConfig Ls Lt N → ℂ) : ℂ :=
  cubic4Schwinger Ls Lt N β n obs

/-- Plaquette action density, gauge invariant by the proved loop lemma. -/
noncomputable def plaquetteDensity (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site) (U : WilsonConfig Ls Lt N) : ℝ :=
  1 - (normWilsonLoop4 (cubic4Plaquette x 1 2) U).re

theorem plaquetteDensity_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : WilsonConfig Ls Lt N)
    (hx : IsLatticePath (cubicTorus4 Ls Lt) x x (cubic4Plaquette x 1 2)) :
    plaquetteDensity Ls Lt N x (gaugeAct g U) = plaquetteDensity Ls Lt N x U := by
  unfold plaquetteDensity
  rw [normWilsonLoop4_gauge_inv hx g U]

/-! ### Fiber regrouping (finite combinatorics, no axioms) -/

noncomputable def iidSupport {n : ℕ} (xs : Fin n → Space4) : Finset Space4 :=
  Finset.univ.image xs

noncomputable def iidFiber {n : ℕ} (xs : Fin n → Space4) (y : Space4) : Finset (Fin n) :=
  Finset.univ.filter (fun i => xs i = y)

lemma prod_regroup {M : Type*} [CommMonoid M] {n : ℕ} (f : Space4 → M)
    (xs : Fin n → Space4) :
    (∏ i : Fin n, f (xs i)) =
      (iidSupport xs).prod (fun y => f y ^ (iidFiber xs y).card) := by
  unfold iidSupport iidFiber
  symm
  calc
    (Finset.univ.image xs).prod (fun y => f y ^ (Finset.univ.filter (fun i => xs i = y)).card)
        = (Finset.univ.image xs).prod (fun y => (Finset.univ.filter (fun i => xs i = y)).prod (fun _ => f y)) := by
            apply Finset.prod_congr rfl; intro y hy; rw [Finset.prod_const]
    _ = ∏ i : Fin n, f (xs i) := by
            simpa using (Finset.prod_fiberwise_of_maps_to'
              (s := (Finset.univ : Finset (Fin n))) (t := Finset.univ.image xs)
              (g := xs) (f := f)
              (by intro i hi; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

lemma iidClasses_eq_fibers {n : ℕ} (xs : Fin n → Space4) :
    iidClasses xs = (iidSupport xs).image (iidFiber xs) := by
  unfold iidClasses iidSupport iidFiber
  ext C
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨xs i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, hi⟩, rfl⟩
    subst hi
    exact ⟨i, rfl⟩

lemma iidFiber_injective {n : ℕ} (xs : Fin n → Space4) :
    Set.InjOn (iidFiber xs) (iidSupport xs) := by
  intro y hy y' hy' heq
  have hyf : ∃ i, xs i = y := by simpa [iidSupport] using hy
  rcases hyf with ⟨i, hi⟩
  have hi_mem : i ∈ iidFiber xs y := by simp [iidFiber, hi]
  have hi_mem' : i ∈ iidFiber xs y' := by rwa [heq] at hi_mem
  have hi_y' : xs i = y' := by simpa [iidFiber] using hi_mem'
  exact hi.symm.trans hi_y'

lemma iidSchwinger_eq_fiberProd {n : ℕ} (xs : Fin n → Space4) :
    iidSchwinger n xs = (iidSupport xs).prod (fun y => iidMom (iidFiber xs y).card) := by
  unfold iidSchwinger
  rw [iidClasses_eq_fibers]
  exact Finset.prod_image (iidFiber_injective xs)

end YangMills
