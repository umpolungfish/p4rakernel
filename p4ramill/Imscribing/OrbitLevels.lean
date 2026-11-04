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

-- Bidirectional orbit: every level orbits the one above and is orbited by the one below.
-- moons (n−1) orbit planets (n), planets orbit stars (n+1), stars orbit the galactic center,
-- and the chain continues indefinitely in both directions.
inductive Orbit : ℤ → ℤ → Prop
| up  : ∀ (n : ℤ), Orbit n (n + 1)
| down : ∀ (n : ℤ), Orbit n (n - 1)

-- Stability operator: a level is "locally stable" when both neighbors are in the set.
def stableOp (S : Set ℤ) : Set ℤ := {n : ℤ | (n - 1 : ℤ) ∈ S ∧ (n + 1 : ℤ) ∈ S}

-- Stable levels are the greatest fixed point of stableOp:
-- the union of all post-fixed points (largest set S such that every member has
-- both neighbors in S). This directly encodes the non-well-founded circular
-- mutual stability of moons ↔ planets ↔ stars ↔ galactic center, with no base case.
def Stable : Set ℤ := ⋃₀ {S : Set ℤ | S ⊆ stableOp S}

-- Every level is stable: Univ is a post-fixed point (every level's neighbors are in Univ),
-- so Univ is in the union, hence every level is in Stable.
theorem all_stable : ∀ (n : ℤ), n ∈ Stable := by
  intro n
  have h : (Set.univ : Set ℤ) ⊆ stableOp (Set.univ : Set ℤ) := by
    intro x _
    trivial
  -- Univ is post-fixed, so every element of Univ is in Stable.
  have h₂ : n ∈ Stable := by
    refine' ⟨Set.univ, h, _⟩
    -- n ∈ Univ
    trivial
  exact h₂

-- No bottom: every level is orbited by a lower level; no level grounds the chain.
theorem no_bottom (n : ℤ) : ∃ m, Orbit m n := by
  refine' ⟨n - 1, _⟩
  have h : Orbit (n - 1) n := by
    have h₁ : Orbit (n - 1) ((n - 1 : ℤ) + 1) := Orbit.up (n - 1)
    have h₂ : ((n - 1 : ℤ) + 1 : ℤ) = n := by ring
    simpa [h₂] using h₁
  exact h

-- No top: every level orbits a higher level; no level caps the chain.
theorem no_top (n : ℤ) : ∃ m, Orbit n m := by
  refine' ⟨n + 1, _⟩
  exact Orbit.up n

-- Every level has both an upward and a downward neighbor — total in both directions.
theorem orbit_total_upward (n : ℤ) : ∃ m, Orbit n m := by
  refine' ⟨n + 1, _⟩
  exact Orbit.up n

theorem orbit_total_downward (n : ℤ) : ∃ m, Orbit m n := by
  refine' ⟨n - 1, _⟩
  have h : Orbit (n - 1) n := by
    have h₁ : Orbit (n - 1) ((n - 1 : ℤ) + 1) := Orbit.up (n - 1)
    have h₂ : ((n - 1 : ℤ) + 1 : ℤ) = n := by ring
    simpa [h₂] using h₁
  exact h

-- Each level is held in place by the levels on either side (mutual stability).
theorem stable_neighbors (n : ℤ) : n - 1 ∈ Stable → n + 1 ∈ Stable → n ∈ Stable := by
  intro h₁ h₂
  -- Get S₁ post-fixed containing n-1
  have h₅ : ∃ (S₁ : Set ℤ), S₁ ⊆ stableOp S₁ ∧ (n - 1 : ℤ) ∈ S₁ := by
    have h₅₁ : (n - 1 : ℤ) ∈ ⋃₀ {S : Set ℤ | S ⊆ stableOp S} := h₁
    -- h₅₁ : ∃ (S₁ : Set ℤ), S₁ ∈ {S | S ⊆ stableOp S} ∧ n - 1 ∈ S₁
    obtain ⟨S₁, hS₁_mem, hS₁₂⟩ := h₅₁
    refine' ⟨S₁, _, hS₁₂⟩
    exact hS₁_mem
  -- Get S₂ post-fixed containing n+1
  have h₆ : ∃ (S₂ : Set ℤ), S₂ ⊆ stableOp S₂ ∧ (n + 1 : ℤ) ∈ S₂ := by
    have h₆₁ : (n + 1 : ℤ) ∈ ⋃₀ {S : Set ℤ | S ⊆ stableOp S} := h₂
    obtain ⟨S₂, hS₂_mem, hS₂₂⟩ := h₆₁
    refine' ⟨S₂, _, hS₂₂⟩
    exact hS₂_mem

  obtain ⟨S₁, hS₁₁, hS₁₂⟩ := h₅
  obtain ⟨S₂, hS₂₁, hS₂₂⟩ := h₆

  -- Let S = {n} ∪ S₁ ∪ S₂. Show S is post-fixed.
  have h₈ : ({n} ∪ S₁ ∪ S₂ : Set ℤ) ⊆ stableOp ({n} ∪ S₁ ∪ S₂) := by
    intro x hx_main
    -- hx_main : x ∈ ({n} ∪ S₁) ∪ S₂
    cases' hx_main with hx_inl hx_inr
    · -- Case A: x ∈ {n} ∪ S₁
      cases' hx_inl with hx_eq hx_in_s1
      · -- x = n
        rw [hx_eq]
        -- n - 1 ∈ S₁, so n - 1 ∈ ({n} ∪ S₁ ∪ S₂)
        have h₁₁ : (n - 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
          exact Or.inl (Or.inr hS₁₂)
        -- n + 1 ∈ S₂, so n + 1 ∈ ({n} ∪ S₁ ∪ S₂)
        have h₁₂ : (n + 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
          exact Or.inr hS₂₂
        dsimp [stableOp]
        exact ⟨h₁₁, h₁₂⟩
      · -- x ∈ S₁
        have h₁₁ : x ∈ stableOp S₁ := hS₁₁ hx_in_s1
        have h₁₂ : (x - 1 : ℤ) ∈ S₁ := by
          dsimp [stableOp] at h₁₁
          exact h₁₁.1
        have h₁₃ : (x + 1 : ℤ) ∈ S₁ := by
          dsimp [stableOp] at h₁₁
          exact h₁₁.2
        -- x - 1 ∈ S₁ ⊆ ({n} ∪ S₁ ∪ S₂)
        have h₁₄ : (x - 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
          exact Or.inl (Or.inr h₁₂)
        -- x + 1 ∈ S₁ ⊆ ({n} ∪ S₁ ∪ S₂)
        have h₁₅ : (x + 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
          exact Or.inl (Or.inr h₁₃)
        dsimp [stableOp]
        exact ⟨h₁₄, h₁₅⟩
    · -- Case B: x ∈ S₂
      have h₁₁ : x ∈ stableOp S₂ := hS₂₁ hx_inr
      have h₁₂ : (x - 1 : ℤ) ∈ S₂ := by
        dsimp [stableOp] at h₁₁
        exact h₁₁.1
      have h₁₃ : (x + 1 : ℤ) ∈ S₂ := by
        dsimp [stableOp] at h₁₁
        exact h₁₁.2
      -- x - 1 ∈ S₂ ⊆ ({n} ∪ S₁ ∪ S₂)
      have h₁₄ : (x - 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
        exact Or.inr h₁₂
      -- x + 1 ∈ S₂ ⊆ ({n} ∪ S₁ ∪ S₂)
      have h₁₅ : (x + 1 : ℤ) ∈ {n} ∪ S₁ ∪ S₂ := by
        exact Or.inr h₁₃
      dsimp [stableOp]
      exact ⟨h₁₄, h₁₅⟩

  -- n ∈ {n} ∪ S₁ ∪ S₂
  have h₉ : n ∈ ({n} ∪ S₁ ∪ S₂ : Set ℤ) := by
    exact Or.inl (by simp)

  -- {n} ∪ S₁ ∪ S₂ is post-fixed and contains n, so n ∈ Stable
  have h₁₀ : n ∈ Stable := by
    refine' ⟨{n} ∪ S₁ ∪ S₂, h₈, _⟩
    exact h₉

  exact h₁₀

-- Level imscription properties.
theorem level_critical (n : ℤ) : (levelImscription n).crit = monad := by rfl
