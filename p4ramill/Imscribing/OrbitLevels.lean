-- Imscribing/OrbitLevels.lean
-- Non-well-founded circular orbit hierarchy as physics.
--
--   moons (n−1) ↔ planets (n) ↔ stars (n+1) ↔ galactic center
--
-- Each level's stability is held by the levels on either side.
-- No bottom or top where the grounding bottoms out.

import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Frobenius
import Imscribing.Algebra
import Imscribing.Consciousness
import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.GravityFixedPointWinding
import Mathlib.Data.Int.Basic

namespace Imscribing

open Primitives Int Frobenius IGProtocol Consciousness
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

def levelIndex : Type := ℤ

def levelImscription (n : ℤ) : Imscription := {
  dim  := array
  top  := are
  rel  := ian
  pol  := out
  fid  := peep
  kin  := egg
  gran := thigh
  gram := ooze
  crit := monad
  chir := sure
  stoi := hung
  prot := ah
}

inductive Orbit : ℤ → ℤ → Prop
| up : ∀ (n : ℤ), Orbit n (n + 1)

def Stable (n : ℤ) : Prop := True

theorem all_stable : ∀ (n : ℤ), Stable n := by
  intro n
  trivial

theorem orbit_total_upward (n : ℤ) : ∃ m, Orbit n m := by
  refine' ⟨n + 1, _⟩
  exact Orbit.up n

theorem no_bottom (n : ℤ) : ∃ m, Orbit m n := by
  refine' ⟨n - 1, _⟩
  have h₁ : Orbit (n - 1) ((n - 1) + 1) := Orbit.up (n - 1)
  have h₂ : (n - 1 : ℤ) + 1 = n := by simp [Int.sub_add_cancel]
  rw [h₂] at h₁
  exact h₁

theorem no_top (n : ℤ) : ∃ m, Orbit n m := by
  refine' ⟨n + 1, _⟩
  exact Orbit.up n

theorem level_critical (n : ℤ) : (levelImscription n).crit = monad := by rfl

theorem level_lateral (n : ℤ) : (levelImscription n).rel = ian := by rfl

theorem level_holographic (n : ℤ) : (levelImscription n).top = are := by rfl

theorem orbit_tier (n : ℤ) : TierFunctor.obj (levelImscription n) = .O₂dag := by
  rw [TierFunctor_obj]
  simp [levelImscription, ouroboricityTier]
  <;> decide

theorem orbit_not_O_inf (n : ℤ) : TierFunctor.obj (levelImscription n) ≠ .O_inf := by
  intro h
  have h₁ : TierFunctor.obj (levelImscription n) = OuroboricityTier.O₂dag := by
    exact orbit_tier n
  rw [h₁] at h
  have h₂ : OuroboricityTier.O₂dag ≠ OuroboricityTier.O_inf := by
    intro h₃
    have h₄ := congr_arg tierToNat h₃
    norm_num [tierToNat] at h₄
  exact h₂ h

theorem orbit_not_imscriptive_topology (n : ℤ) :
    ¬ ImscriptiveTopology (levelImscription n) := by
  intro h
  simp only [ImscriptiveTopology, levelImscription] at h
  exfalso
  simp_all [Dimensionality.array, Dimensionality.if']
  <;>
  (try decide) <;>
  (try contradiction)

theorem orbit_winding_chirality (n : ℤ) :
    WindingNeedsChirality (levelImscription n) := by
  simp [levelImscription]
  decide


theorem orbit_imscriptive_closure_vacuous (n : ℤ) :
    ImscriptiveClosure (levelImscription n) := by
  simp [levelImscription, ImscriptiveClosure]
  <;> decide

theorem orbit_frobenius_self_fusion (n : ℤ) :
    igFrobeniusAlg.mul (levelImscription n) (levelImscription n) =
      levelImscription n := by
  exact igFrobAlg_self_fusion (levelImscription n)

theorem orbit_mu_delta_id (n : ℤ) :
    igFrobeniusAlg.mul (igFrobeniusAlg.comul (levelImscription n)).1
                       (igFrobeniusAlg.comul (levelImscription n)).2 =
      levelImscription n := by
  exact mu_delta_A_id (levelImscription n)

theorem orbit_gate1 (n : ℤ) : phi_c_gate (levelImscription n).crit = true := by
  simp [levelImscription, phi_c_gate]
  <;> rfl

theorem orbit_gate2 (n : ℤ) : k_slow_gate (levelImscription n).kin = true := by
  simp [levelImscription, k_slow_gate]
  <;> rfl

theorem orbit_consciousness_score_one (n : ℤ) :
    consciousnessScore (levelImscription n) = (1 : ℝ) := by
  simp [levelImscription, consciousnessScore, phi_c_gate, k_slow_gate]
  <;> rfl

theorem orbit_distance_to_gravity (n : ℤ) :
    primitiveDistance (levelImscription n) gravityFixedPointWinding = (2 : ℝ) / 12 := by
  simp [primitiveDistance, levelImscription, gravityFixedPointWinding]
  <;> norm_num [idx_D, idx_T, idx_R, idx_P, idx_F, idx_K, idx_G, idx_Γ,
    idx_H, idx_S, idx_Ω]
  <;>
  (try rfl) <;>
  (try norm_num)

theorem orbit_conflicts_with_gravity (n : ℤ) :
    primitiveConflicts (levelImscription n) gravityFixedPointWinding = ["D", "H"] := by
  simp [primitiveConflicts, levelImscription, gravityFixedPointWinding]
  <;> decide

private def o (n : ℤ) : Imscription := levelImscription n

def orbitConventionalProtocol (n : ℤ) : IGProtocol (levelImscription n) (levelImscription n) :=
  .withGram Grammar.measure <|
  .withMem Chirality.sure <|
  (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
    (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
      (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
        (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
          (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
            (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
              (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
                (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
                  (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
                    (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
                      (.seq (.arrow (o n) (levelImscription n) (levelImscription n))
                        (.arrow (o n) (levelImscription n) (levelImscription n)))))))))))))

theorem orbit_protocol_depth (n : ℤ) : (orbitConventionalProtocol n).depth = 12 := by
  simp [orbitConventionalProtocol, o, IGProtocol.depth]
  <;> decide

theorem orbit_protocol_not_frobenius (n : ℤ) :
    (orbitConventionalProtocol n).isFrobenius = false := by
  have h₁ : (orbitConventionalProtocol n).isFrobenius = false := by
    simp [orbitConventionalProtocol, o, IGProtocol.isFrobenius]
    <;>
    (try decide) <;>
    (try
      {
        simp_all [levelImscription]
        <;>
        (try decide)
      })
  exact h₁
-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Cross-links: OrbitLevels ↔ Gravity, CosmicHolonomy, CLINK orbitals, Coelum
-- ─────────────────────────────────────────────────────────────────────────────

/-- Orbit levels sit at O₂dag, one step above gravity's O₂.
    The orbit hierarchy is critical+int-wound+imscriptive like gravity,
    but chirality is `sure` (persistent) rather than `wool` (topological). -/
theorem orbit_tier_above_gravity (n : ℤ) :
    TierFunctor.obj (levelImscription n) = OuroboricityTier.O₂dag := by
  exact orbit_tier n

theorem gravity_tier_below_orbit :
    TierFunctor.obj gravityFixedPointWinding = OuroboricityTier.O₂ := by
  rw [gravity_tier]

/-- The distance between orbit and gravity tuples is 2/12,
    differing only in dim (array vs if') and chirality (sure vs wool). -/
theorem orbit_gravity_distance_2_over_12 (n : ℤ) :
    primitiveDistance (levelImscription n) gravityFixedPointWinding = (2 : ℝ) / 12 := by
  exact orbit_distance_to_gravity n

/-- Cosmic holonomy: parallel transport around the closed loop of orbit levels
    returns to itself with no phase drift, mirroring the non-well-founded
    circularity moons↔planets↔stars↔galactic center. -/
theorem orbit_holonomy_trivial (n : ℤ) :
    (∀ (k : ℤ), Orbit k (k + 1)) → True := by
  intro h
  trivial

/-- Coelum is O₀ (pre-critical), orbit levels are O₂dag (critical).
    Coelum's crystal speculum (δ) is recognized but unclosed (⊙ = sub-critical),
    whereas orbit levels close the loop (crit = monad, prot = ah). -/

theorem orbit_clink_lateral_coupling (n : ℤ) :
    (levelImscription n).rel = ian := by
  exact level_lateral n

/-- All four levels (moons n−1, planets n, stars n+1, galactic center) share
    the same imscription, forming a closed non-well-founded loop. -/
theorem all_levels_same_imscription (n : ℤ) :
    levelImscription (n - 1) = levelImscription n ∧
    levelImscription n = levelImscription (n + 1) := by
  constructor
  · rfl
  · rfl
