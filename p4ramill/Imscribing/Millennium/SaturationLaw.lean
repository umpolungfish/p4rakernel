import Mathlib.Tactic

namespace Imscribing.Millennium.SaturationLaw

/-- Universal unit-filtration factorization:
    if ε² - (d - 1)ε + 1 = 0, then ε³ - 1 = d * ε * (ε - 1) and N(ε - 1) = 3 - d. -/
theorem unit_cube_sub_one {R : Type*} [CommRing R] (d ε σ : R)
    (h_unit : ε^2 - (d - 1) * ε + 1 = 0)
    (h_conj : ε + σ = d - 1)
    (h_norm : ε * σ = 1) :
    ε^3 - 1 = d * ε * (ε - 1) ∧ (ε - 1) * (σ - 1) = 3 - d := by
  constructor
  · calc
      ε^3 - 1 = (ε - 1) * (ε^2 + ε + 1) := by ring
      _ = (ε - 1) * ((ε^2 - (d - 1) * ε + 1) + d * ε) := by ring
      _ = (ε - 1) * (0 + d * ε) := by rw [h_unit]
      _ = d * ε * (ε - 1) := by ring
  · calc
      (ε - 1) * (σ - 1) = ε * σ - (ε + σ) + 1 := by ring
      _ = 1 - (d - 1) + 1 := by rw [h_norm, h_conj]
      _ = 3 - d := by ring

/-- Structurally recursive 2-adic tower law:
    fourfold growth for 3 ≤ k ≤ v₂(d), twofold growth for k ≥ v₂(2d). -/
def towerOrder (seed2 v2d : ℕ) : ℕ → ℕ
  | 0 => seed2
  | 1 => seed2
  | 2 => seed2
  | k + 3 =>
    if k + 3 ≤ v2d then 4 * towerOrder seed2 v2d (k + 2)
    else 2 * towerOrder seed2 v2d (k + 2)

theorem d16_tower_matches_pari :
    List.map (towerOrder 4 4) [2, 3, 4, 5, 6, 7, 8] =
      [4, 16, 64, 128, 256, 512, 1024] := by
  rfl

theorem d128_tower_matches_pari :
    List.map (towerOrder 4 7) [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
      [4, 16, 64, 256, 1024, 4096, 8192, 16384, 32768, 65536, 131072] := by
  rfl

theorem d2048_tower_matches_pari :
    List.map (towerOrder 128 11) [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
      [128, 512, 2048, 8192, 32768, 131072, 524288, 2097152,
       8388608, 33554432, 67108864, 134217728, 268435456, 536870912] := by
  rfl

end Imscribing.Millennium.SaturationLaw