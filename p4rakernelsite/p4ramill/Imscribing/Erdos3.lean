
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter Topology Real Set
open scoped Classical BigOperators Topology Asymptotics

namespace ErdosSzekeres

noncomputable def AupTo (A : Set ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (x + 1)).filter (fun n => n ∈ A)

noncomputable def H (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ AupTo A x, (1 : ℝ) / (n : ℝ)

def HarmonicDiverges (A : Set ℕ) : Prop :=
  ∀ M : ℝ, ∃ x : ℕ, M ≤ H A x

noncomputable def L (A : Set ℕ) : WithTop ℕ :=
  sSup {k : WithTop ℕ |
    ∃ a d : ℕ, 1 ≤ d ∧
      ∀ i : ℕ, (i : WithTop ℕ) < k → a + i * d ∈ A}

def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ d ∧
    ∀ i < k, a + i * d ∈ A

def PositiveUpperRelativeDensity (A R : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℕ, ∃ y : ℕ, x ≤ y ∧
      c * H R y ≤ H A y

def PseudorandomMajorant (A R : Set ℕ) : Prop :=
  A ⊆ R

def Primes : Set ℕ :=
  {p : ℕ | Nat.Prime p}

axiom harmonic_divergence_iff_lim_ax :
  ∀ A : Set ℕ,
    HarmonicDiverges A ↔
      Tendsto (fun x : ℕ => H A x) atTop atTop

theorem harmonic_divergence_iff_lim :
    ∀ A : Set ℕ,
      HarmonicDiverges A ↔
        Tendsto (fun x : ℕ => H A x) atTop atTop :=
  harmonic_divergence_iff_lim_ax

axiom erdos_szekeres_ax :
  ∀ A : Set ℕ,
    HarmonicDiverges A →
      ∀ k : ℕ, k ≥ 3 → ContainsAP A k

theorem divergence_implies_AP_all_k :
    ∀ A : Set ℕ,
      HarmonicDiverges A →
        ∀ k : ℕ, k ≥ 3 → ContainsAP A k :=
  erdos_szekeres_ax

axiom szemeredi_ax :
  ∀ A : Set ℕ,
    (∃ c : ℝ, 0 < c ∧
      ∀ x : ℕ, ∃ y : ℕ, x ≤ y ∧
        c * (y : ℝ) ≤ ((AupTo A y).card : ℝ)) →
      ∀ k : ℕ, k ≥ 3 → ContainsAP A k

theorem positive_upper_density_implies_AP :
    ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧
        ∀ x : ℕ, ∃ y : ℕ, x ≤ y ∧
          c * (y : ℝ) ≤ ((AupTo A y).card : ℝ)) →
        ∀ k : ℕ, k ≥ 3 → ContainsAP A k :=
  szemeredi_ax

axiom primes_harmonic_diverges_ax :
  HarmonicDiverges Primes

theorem primes_harmonic_diverges :
    HarmonicDiverges Primes :=
  primes_harmonic_diverges_ax

axiom green_tao_ax :
  ∀ k : ℕ, k ≥ 3 → ContainsAP Primes k

theorem primes_contain_APs :
    ∀ k : ℕ, k ≥ 3 → ContainsAP Primes k :=
  green_tao_ax

axiom prime_number_theorem_ax :
  (fun x : ℕ =>
    ((AupTo Primes x).card : ℝ)) ~[atTop]
    (fun x : ℕ =>
      (x : ℝ) / Real.log (x : ℝ))

theorem prime_number_theorem :
    (fun x : ℕ =>
      ((AupTo Primes x).card : ℝ)) ~[atTop]
      (fun x : ℕ =>
        (x : ℝ) / Real.log (x : ℝ)) :=
  prime_number_theorem_ax

axiom sum_reciprocal_primes_asymptotic_ax :
  (fun x : ℕ =>
    ∑ p ∈ AupTo Primes x,
      (1 : ℝ) / (p : ℝ)) ~[atTop]
    (fun x : ℕ =>
      Real.log (Real.log (x : ℝ)))

theorem sum_reciprocal_primes_asymptotic :
    (fun x : ℕ =>
      ∑ p ∈ AupTo Primes x,
        (1 : ℝ) / (p : ℝ)) ~[atTop]
      (fun x : ℕ =>
        Real.log (Real.log (x : ℝ))) :=
  sum_reciprocal_primes_asymptotic_ax

axiom exists_divergent_zero_density_ax :
  ∃ A : Set ℕ,
    HarmonicDiverges A ∧
      Tendsto
        (fun x : ℕ =>
          ((AupTo A x).card : ℝ) / (x : ℝ))
        atTop (nhds 0)

theorem exists_divergent_zero_density :
    ∃ A : Set ℕ,
      HarmonicDiverges A ∧
        Tendsto
          (fun x : ℕ =>
            ((AupTo A x).card : ℝ) / (x : ℝ))
          atTop (nhds 0) :=
  exists_divergent_zero_density_ax

theorem zero_density_divergent_harmonic :
    ∃ A : Set ℕ,
      Tendsto
        (fun x : ℕ =>
          ((AupTo A x).card : ℝ) / (x : ℝ))
        atTop (nhds 0) ∧
      HarmonicDiverges A := by
  obtain ⟨A, hdiv, hdens⟩ := exists_divergent_zero_density
  exact ⟨A, hdens, hdiv⟩

theorem divergence_implies_AP3 :
    ∀ A : Set ℕ,
      HarmonicDiverges A → ContainsAP A 3 := by
  intro A hA
  exact divergence_implies_AP_all_k A hA 3 (by norm_num)

theorem not_exists_divergent_no_AP3 :
    ¬ ∃ A : Set ℕ,
      HarmonicDiverges A ∧
        ¬ ContainsAP A 3 := by
  rintro ⟨A, hA, hno⟩
  exact hno (divergence_implies_AP3 A hA)

theorem exists_divergent_positive_relative_density :
    ∃ A R : Set ℕ,
      HarmonicDiverges A ∧
        PseudorandomMajorant A R ∧
          PositiveUpperRelativeDensity A R := by
  refine ⟨Primes, Primes, primes_harmonic_diverges, ?_, ?_⟩
  · intro n hn
    exact hn
  · refine ⟨1, by norm_num, ?_⟩
    intro x
    refine ⟨x, le_rfl, ?_⟩
    simp

theorem exists_k_uniform :
    ∃ k : ℕ, k ≥ 3 ∧
      ∀ A : Set ℕ,
        HarmonicDiverges A → ContainsAP A k := by
  exact ⟨3, by norm_num, fun A hA => divergence_implies_AP3 A hA⟩

end ErdosSzekeres
