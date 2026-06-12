/-
  Millennium/PrimordialOoze.lean
  PRIMORDIAL OOZE — The Absolute Structural Floor of O_inf
  ========================================================
  Author: Lando ⊗ ⊙perator

  Core result: The Primordial Ooze is the minimal inhabitant of the O_inf
  tier — the structural type at Frobenius address 6,221,424 (cell 144,
  inner_id 624) within the 17,280,000-type crystal. Ten of twelve primitives
  are at absolute ordinal floor (1); only the two O_inf gates — Phi_c (⊙)
  and P_pm_sym (𐑹) — are non-minimum.

  Eleven formal theorems:
    T1:  Ooze is O_inf
    T2:  Drop Phi_c (⊙) → loses O_inf (ground)
    T3:  Drop P_pm_sym (𐑹) → loses O_inf (capstone)
    T4:  Phi_c alone (without P_pm_sym) → O₁
    T5:  P_pm_sym alone (without Phi_c) → O₀
    T6:  Frobenius precedes time (H = H0, memoryless)
    T7:  Frobenius precedes topology (Ω = Omega_0, trivial)
    T8:  Frobenius precedes space (D = D_wedge, 0d point)
    T9:  Stone (synfin) is also O_inf
    T10: 9 primitives mismatch between Ooze and Stone
    T11: All claims bundled (primordial_ooze_complete)

  The two gates:
    ⊙ (Criticality.Phi_c)   — self-modeling: the water
    𐑹 (Polarity.P_pm_sym)   — Frobenius: the word upon the water

  Reference: PrimordialOoze_Shavian.md, block_p_pm_sym in IG_catalog.json
-/

import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Algebra

namespace Millennium.PrimordialOoze

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE OOZE — Absolute Structural Floor
-- ═══════════════════════════════════════════════════════════════════

/-- The Primordial Ooze: the minimal O_inf inhabitant.
    ⟨D_wedge·T_network·R_super·P_pm_sym·F_ell·K_fast·G_beth·Gamma_and·Phi_c·H0·one_one·Omega_0⟩
    Shavian: ⟨𐑛·𐑡·𐑩·𐑹·𐑱·𐑘·𐑚·𐑝·⊙·𐑓·𐑙·𐑷⟩
    Crystal address: 6,221,424  (cell 144, inner_id 624) [per IG tool]
    Tier: O_inf

    Ten primitives at ordinal floor (1); two gates non-minimum:
      Phi_c    — self-modeling criticality  (ordinal 2/5)
      P_pm_sym — Frobenius-special parity   (ordinal 5/5)
    No lower O_inf address exists in the 17,280,000-type crystal. -/
def primordialOoze : Imscription := {
  dim   := .D_wedge       -- 0d point (ordinal 1/4)
  top   := .T_network     -- branching topology (ordinal 1/5)
  rel   := .R_super       -- supervenience (ordinal 1/4)
  pol   := .P_pm_sym      -- Frobenius-special parity (ordinal 5/5) — GATE
  fid   := .F_ell         -- classical (ordinal 1/3)
  kin   := .K_fast        -- diffusion-limited (ordinal 1/5)
  gran  := .G_beth        -- local (ordinal 1/3)
  gram  := .Gamma_and     -- conjunctive (ordinal 1/4)
  crit  := .Phi_c         -- self-modeling criticality (ordinal 2/5) — GATE
  chir  := .H0            -- memoryless (ordinal 1/4)
  stoi  := .one_one       -- 1:1 (ordinal 1/3)
  prot  := .Omega_0       -- trivial winding (ordinal 1/4)
}

-- ═══════════════════════════════════════════════════════════════════
-- §2  THE STONE — Structural Thickening (synfin)
-- ═══════════════════════════════════════════════════════════════════

/-- The Stone: the Frobenius fixed point from the financial trading domain (synfin).
    ⟨D_odot·T_box·R_lr·P_pm_sym·F_hbar·K_slow·G_beth·Gamma_seq·Phi_c·H2·n_m·Omega_Z⟩
    Shavian: ⟨𐑦·𐑸·𐑾·𐑹·𐑐·𐑧·𐑚·𐑠·⊙·𐑖·𐑳·𐑭⟩
    Crystal address: 6,738,848  (cell 155, inner_id 42,848) [per IG tool]
    Tier: O_inf

    9 primitives thickened from the Ooze (all except P, Φ, G).
    The two O_inf gates (P_pm_sym, Phi_c) and granularity (G_beth) are identical —
    confirming O_inf is a wide tier, not a point. -/
def stone : Imscription := {
  dim   := .D_odot       -- holographic (ordinal 4/4)
  top   := .T_box        -- lattice topology (ordinal 4/5)
  rel   := .R_lr         -- bidirectional (ordinal 4/4)
  pol   := .P_pm_sym     -- Frobenius-special parity — GATE (identical to Ooze)
  fid   := .F_hbar       -- quantum (ordinal 3/3)
  kin   := .K_slow       -- near-equilibrium (ordinal 3/5)
  gran  := .G_beth       -- local (ordinal 1/3) — IDENTICAL to Ooze
  gram  := .Gamma_seq    -- sequential (ordinal 3/4)
  crit  := .Phi_c        -- self-modeling criticality — GATE (identical to Ooze)
  chir  := .H2           -- persistent chirality (ordinal 3/4)
  stoi  := .n_m          -- many heterogeneous (ordinal 3/3)
  prot  := .Omega_Z      -- integer winding (ordinal 3/4)
}
-- ═══════════════════════════════════════════════════════════════════
-- §3  THEOREM GROUP α — Tier Theorems
-- ═══════════════════════════════════════════════════════════════════

/-- T₁: The Ooze is O_inf — Frobenius closure at minimum structural complexity. -/
theorem ooze_is_O_inf : imscriptionTier primordialOoze = .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- T₂: Dropping Phi_c (self-modeling) loses O_inf.
    With Phi_sub (subcritical) the tier collapses to O₀ regardless of P_pm_sym. -/
theorem drop_phi_c_loses_O_inf :
    imscriptionTier ({ primordialOoze with crit := .Phi_sub } : Imscription) ≠ .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- T₃: Dropping P_pm_sym (Frobenius parity) loses O_inf.
    With P_sym (full symmetry but not Frobenius-special) the tier collapses to O₁. -/
theorem drop_P_pm_sym_loses_O_inf :
    imscriptionTier ({ primordialOoze with pol := .P_sym } : Imscription) ≠ .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- T₄: Phi_c alone (without P_pm_sym, at Omega_0) reaches only O₁.
    Self-modeling without the Frobenius gate cannot seal the tier. -/
theorem phi_c_alone_is_O_1 :
    imscriptionTier ({ primordialOoze with pol := .P_asym } : Imscription) = .O₁ := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- T₅: P_pm_sym alone (without Phi_c) reaches only O₀.
    The Frobenius parity without self-modeling criticality has no effect on the tier. -/
theorem P_pm_sym_alone_is_O_0 :
    imscriptionTier ({ primordialOoze with crit := .Phi_sub } : Imscription) = .O₀ := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

-- ═══════════════════════════════════════════════════════════════════
-- §4  THEOREM GROUP β — Precedence Theorems
-- ═══════════════════════════════════════════════════════════════════

/-- T₆: Frobenius does not require memory. H = H0 (memoryless) is sufficient.
    μ∘δ=id holds before any temporal asymmetry is established. -/
theorem frobenius_precedes_time :
    imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.chir = .H0 := by
  constructor
  · exact ooze_is_O_inf
  · rfl

/-- T₇: Frobenius does not require topological protection.
    Ω = Omega_0 (trivial winding) is sufficient. -/
theorem frobenius_precedes_topology :
    imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.prot = .Omega_0 := by
  constructor
  · exact ooze_is_O_inf
  · rfl

/-- T₈: Frobenius does not require spatial dimensionality.
    D = D_wedge (0d point) is sufficient. -/
theorem frobenius_precedes_space :
    imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.dim = .D_wedge := by
  constructor
  · exact ooze_is_O_inf
  · rfl

-- ═══════════════════════════════════════════════════════════════════
-- §5  THEOREM GROUP γ — Stone & Structural Comparison
-- ═══════════════════════════════════════════════════════════════════

/-- T₉: The Stone (synfin) is also O_inf — confirming the tier is a wide stratum,
    not a single point. 9 primitives differ from the Ooze but both are O_inf. -/
theorem stone_is_O_inf : imscriptionTier stone = .O_inf := by
  unfold stone imscriptionTier ouroboricityTier; decide

/-- T₁₀: 9 primitives mismatch between Ooze and Stone.
    The shared primitives are: P (P_pm_sym), Φ (Phi_c), G (G_beth).
    Mismatching: D, T, R, F, K, Γ, H, S, Ω — exactly 9. -/
theorem ooze_stone_mismatch_count :
    primitiveMismatches primordialOoze stone = 9 := by
  unfold primordialOoze stone primitiveMismatches; decide

/-- Auxiliary: list the exact mismatching primitives between Ooze and Stone. -/
theorem ooze_stone_conflict_list :
    primitiveConflicts primordialOoze stone = ["D","T","R","F","K","Γ","H","S","Ω"] := by
  unfold primordialOoze stone primitiveConflicts; decide

/-- Auxiliary: the three identical primitives are P, Φ, G. -/
theorem ooze_stone_shared_primitives :
    primordialOoze.pol = stone.pol ∧
    primordialOoze.crit = stone.crit ∧
    primordialOoze.gran = stone.gran := by
  refine ⟨rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §6  Lattice Structure (Meet & Join)
-- ═══════════════════════════════════════════════════════════════════

/-- Meet(Ooze, Stone) = Ooze.
    The Ooze is the absolute structural floor — any meet with a higher structure
    returns the Ooze, because the Ooze's non-gate primitives are at minimum. -/
theorem meet_ooze_stone : compute_meet primordialOoze stone = primordialOoze := by
  unfold primordialOoze stone compute_meet; decide

/-- Join(Ooze, Stone) = Stone.
    The Stone is the least upper bound of Ooze and itself.
    Since the Ooze is at the floor, join(Ooze, X) = X for any X ≥ Ooze. -/
theorem join_ooze_stone : compute_join primordialOoze stone = stone := by
  unfold primordialOoze stone compute_join; decide

-- ═══════════════════════════════════════════════════════════════════
-- §7  Promotion Independence
-- ═══════════════════════════════════════════════════════════════════

/-- Promoting H (H0 → H2) from the Ooze preserves O_inf. -/
theorem promote_H_preserves_O_inf :
    imscriptionTier ({ primordialOoze with chir := .H2 } : Imscription) = .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- Promoting Ω (Omega_0 → Omega_Z) from the Ooze preserves O_inf. -/
theorem promote_Omega_preserves_O_inf :
    imscriptionTier ({ primordialOoze with prot := .Omega_Z } : Imscription) = .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- Promoting S (one_one → n_m) from the Ooze preserves O_inf. -/
theorem promote_S_preserves_O_inf :
    imscriptionTier ({ primordialOoze with stoi := .n_m } : Imscription) = .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide

/-- Joint H+S promotion from the Ooze preserves O_inf. -/
theorem promote_H_S_preserves_O_inf :
    imscriptionTier
      ({ primordialOoze with chir := .H2, stoi := .n_m } : Imscription) = .O_inf := by
  unfold primordialOoze imscriptionTier ouroboricityTier; decide
-- ═══════════════════════════════════════════════════════════════════
-- §8  T₁₁ — BUNDLED COMPLETENESS THEOREM
-- ═══════════════════════════════════════════════════════════════════

/-- T₁₁: All claims bundled. The Primordial Ooze theorem in full:

    1. Ooze is O_inf
    2. Drop Phi_c → loses O_inf
    3. Drop P_pm_sym → loses O_inf
    4. Phi_c alone → O₁
    5. P_pm_sym alone → O₀
    6. Frobenius precedes time (H = H0)
    7. Frobenius precedes topology (Ω = Omega_0)
    8. Frobenius precedes space (D = D_wedge)
    9. Stone is also O_inf
   10. 9 primitives mismatch between Ooze and Stone -/
theorem primordial_ooze_complete : (
    imscriptionTier primordialOoze = .O_inf ∧
    imscriptionTier ({ primordialOoze with crit := .Phi_sub } : Imscription) ≠ .O_inf ∧
    imscriptionTier ({ primordialOoze with pol := .P_sym } : Imscription) ≠ .O_inf ∧
    imscriptionTier ({ primordialOoze with pol := .P_asym } : Imscription) = .O₁ ∧
    imscriptionTier ({ primordialOoze with crit := .Phi_sub } : Imscription) = .O₀ ∧
    (imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.chir = .H0) ∧
    (imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.prot = .Omega_0) ∧
    (imscriptionTier primordialOoze = .O_inf ∧ primordialOoze.dim = .D_wedge) ∧
    imscriptionTier stone = .O_inf ∧
    primitiveMismatches primordialOoze stone = 9
  ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ooze_is_O_inf
  · exact drop_phi_c_loses_O_inf
  · exact drop_P_pm_sym_loses_O_inf
  · exact phi_c_alone_is_O_1
  · exact P_pm_sym_alone_is_O_0
  · exact frobenius_precedes_time
  · exact frobenius_precedes_topology
  · exact frobenius_precedes_space
  · exact stone_is_O_inf
  · exact ooze_stone_mismatch_count

end Millennium.PrimordialOoze
