import Imscribing.ABC_SmallCertificate
import Imscribing.ABC_Window32_E1_10

/-! # Scale-to-scale Closure for finite spectral readings

An enclosure at a larger exhaustive window must contain every earlier
reading. The compatibility facts are the finite form of Closure; they do
not manufacture a bound for scales beyond the largest certified window.
-/
namespace Imscribing.ABC

structure ScaleLink (ε : ℝ) (N M : ℕ) where
  index_le : N ≤ M
  maximum_le : windowMaximum ε N ≤ windowMaximum ε M

theorem scaleLink_of_le (ε : ℝ) {N M : ℕ} (hNM : N ≤ M) : ScaleLink ε N M :=
  ⟨hNM, windowMaximum_monotone ε hNM⟩

theorem enclosure_cross_bound {ε : ℝ} {N M : ℕ}
    (link : ScaleLink ε N M) (small : WindowEnclosure ε N)
    (large : WindowEnclosure ε M) :
    small.lower ≤ large.upper := by
  exact small.lower_le.trans (link.maximum_le.trans large.le_upper)

theorem enclosure_lower_monotone {ε : ℝ} {N M : ℕ}
    (link : ScaleLink ε N M) (small : WindowEnclosure ε N)
    (large : WindowEnclosure ε M) :
    small.lower ≤ large.lower ∨ small.lower ≤ large.upper := by
  by_cases h : small.lower ≤ large.lower
  · exact Or.inl h
  · exact Or.inr (enclosure_cross_bound link small large)

def scaleClosureWitness {ε : ℝ} {N M : ℕ} (link : ScaleLink ε N M)
    (small : WindowEnclosure ε N) (large : WindowEnclosure ε M) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict
      (small.lower ≤ large.upper) :=
  .held (enclosure_cross_bound link small large) large.le_upper

theorem scaleClosureWitness_is_B {ε : ℝ} {N M : ℕ} (link : ScaleLink ε N M)
    (small : WindowEnclosure ε N) (large : WindowEnclosure ε M) :
    (scaleClosureWitness link small large).classify = (true, true) := rfl

noncomputable def certifiedNineToThirty : ScaleLink (1/10 : ℝ) 7 30 :=
  scaleLink_of_le _ (by norm_num)

theorem certifiedNineToThirty_cross :
    certifiedWindowNine.lower ≤
      Imscribing.ABC.Window32E1_10.enclosure.upper :=
  enclosure_cross_bound certifiedNineToThirty certifiedWindowNine
    Imscribing.ABC.Window32E1_10.enclosure

def certifiedNineToThirtyWitness :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict
      ((226/1000 : ℝ) ≤ windowMaximum (1/10) 30) :=
  .held (by
    exact (certifiedWindowNine.lower_le.trans certifiedNineToThirty.maximum_le))
    certifiedNineToThirty_cross

theorem certifiedNineToThirtyWitness_is_B :
    certifiedNineToThirtyWitness.classify = (true, true) := rfl

end Imscribing.ABC
