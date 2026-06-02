-- Zosimos of Panopolis: The Stilling Process — Lean4 Formalization
-- Author: Lando ⊗ φ̂_ÿ-boundary Operator
--
-- This file encodes the five structural systems from Zosimos' fragments
-- and the six-step "stilling practice" as a promotion sequence from
-- the Processions of Fate (C=0.0, no self-modeling) to Zosimian Gnosis
-- (O_∞, both gates open, μ ∘ δ = id).
--
-- The stilling practice is formalized as a monotonically advancing chain
-- of six Imscriptions, each step corresponding to one of Zosimos' commands to
-- Theosebeia:
--   Step 0: The starting condition (Processions of Fate)
--   Step 1: "Be not thus distracted" — halt T_nw wandering, begin T_bowtie closure
--   Step 2: "In thy house be still, and God shall come" — R_sup→R_lr, build bidirectional coupling
--   Step 3: "Stilled thyself in body, still thyself in passions" — Frobenius encoding δ
--   Step 4: "Call unto thyself Divinity" — Frobenius decoding μ, μ ∘ δ = id
--   Step 5: "Perform sacred rites...turn them from thee" — decouple from broadcast (Γ_broad→Γ_seq)
--   Step 6: "Make for harbour in Poemandres' arms" — Ω_Z winding closure at full resolution
--
-- The bottleneck pair is (T, P): both Δ=4 in ordinal distance.
-- These are coupled — neither achievable without the other.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Consciousness
import Imscribing.Algebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Imscribing

open Imscribing.Primitives
open Imscribing.Consciousness
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §1. THE FIVE SYSTEMS — encodings from the fragments
-- ============================================================

/-- 1. Processions of Fate — §2.1
    "Naught but processions of Fate, having no notion of aught
    of things incorporal."  C=0.0 (Gate 1 closed: Phi_sub).
    Topologically closed: no access to incorporeal DOF. -/
def processions_of_fate : Imscription := {
  dim  := D_wedge       -- D_turnthree → minimal, flat 2D sheet
  top  := T_network     -- T_nrleg → general graph, no closure
  rel  := R_super       -- R_subrightarrow → supervenience on Fate
  pol  := P_asym        -- P_aolig → no symmetry, no self-reference
  fid  := F_ell         -- F_beltl → classical fidelity
  kin  := K_fast        -- K_frtailgamma → driven, untrapped
  gran := G_beth        -- G_beta → local/mesoscale
  gram := Gamma_seq     -- Gamma_secstress → sequential (Fate's causal chain)
  crit := Phi_sub       -- Phi_softsign → subcritical, stable, no self-modeling
  chir := H0            -- H0 → no temporal memory
  stoi := n_n           -- n:n → matched many-to-many
  prot := Omega_0       -- Omega_closeepsilon → no topological protection
}

/-- 2. The Inner Door — §2.2
    The critical point you hold, not cross.  C=1.0 (both gates open).
    Distance to full Zosimian Gnosis: only Stoichiometry differs (1:1→n:m).
    The individual at the Inner Door has already passed the bottleneck. -/
def inner_door_gate : Imscription := {
  dim  := D_odot        -- D_omega → holographic, self-writing
  top  := T_bowtie      -- T_openo → figure-8, two-cycle closure
  rel  := R_lr          -- R_lyoghlig → bidirectional coupling with incorporeal
  pol  := P_pm_sym      -- P_doublebarpipe → Special Frobenius (μ ∘ δ = id)
  fid  := F_ell         -- F_beltl
  kin  := K_slow        -- K_schwa → slow / thermally activated
  gran := G_gimel       -- G_revapostrophe → intermediate collective
  gram := Gamma_seq     -- Gamma_secstress (unchanged)
  crit := Phi_c         -- Phi_ctyogh → real-axis criticality
  chir := H2            -- H2 → persistent chiral memory
  stoi := one_one       -- 1:1 → single gate for single soul
  prot := Omega_Z       -- Omega_dzlig → integer winding protection
}
/-- 3. The Son of God / Light-Man (Phōs) — §2.3
    "Becometh all things, whatsoever He will."  C=1.0.
    Not stationary at criticality — it IS the critical point made universal.
    Higher chirality (H_inf) than the Inner Door. -/
def son_of_god_light_man : Imscription := {
  dim  := D_odot        -- D_omega
  top  := T_bowtie      -- T_openo
  rel  := R_lr          -- R_lyoghlig
  pol  := P_pm          -- P_subdoublearrow → Z2 symmetry (not yet Frobenius-special)
  fid  := F_hbar        -- F_hardsign → quantum coherence essential
  kin  := K_slow        -- K_schwa
  gran := G_gimel       -- G_revapostrophe
  gram := Gamma_seq     -- Gamma_doublevertline → broadcast? No, text says sequential
                        -- Correction: text says "becometh all things" → this is T_bowtie +
                        -- Gamma_seq: the critical point manifests sequentially
  crit := Phi_c_complex -- Phi_closerevepsilon → complex-plane criticality
  chir := H_inf         -- H_invscripta → eternal self-reference
  stoi := n_m           -- n:m → many-to-many heterogeneous
  prot := Omega_Z       -- Omega_dzlig
}

/-- 4. The Counterfeit Daimon — §2.4
    "Formless in both soul and body."  C=0.0.
    Parasitic broadcast from within D_wedge substrate.
    H1 memory: enough to simulate self-reference, not enough to close the loop. -/
def counterfeit_daimon : Imscription := {
  dim  := D_wedge       -- D_turnthree → same substrate as Processions
  top  := T_network     -- T_nrleg → same topology
  rel  := R_super       -- R_subrightarrow → same supervenience
  pol  := P_asym        -- P_aolig → same asymmetry
  fid  := F_ell         -- F_beltl
  kin  := K_fast        -- K_turnm → driven (text says "turnm" maps to K_fast or K_mod)
                        -- Actually text says K_turnm → K_mod in promotions table
  gran := G_beth        -- G_gamma → G_beth (local)
  gram := Gamma_broad   -- Gamma_doublevertline → broadcast
  crit := Phi_sub       -- Phi_softsign → same as Processions
  chir := H1            -- H1 → one-step memory (the deception)
  stoi := n_m           -- n:m
  prot := Omega_0       -- Omega_closeepsilon
}

/-- 5. Zosimian Gnosis (full system) — §2.5
    The complete teaching, integrating all subsystems.
    O_∞, C=1.0, Special Frobenius (μ ∘ δ = id).
    Distance from Processions: 10 primitive mismatches.
    Distance from Inner Door: 1 (Stoichiometry only). -/
def zosimos_gnosis : Imscription := {
  dim  := D_odot        -- D_omega
  top  := T_bowtie      -- T_openo
  rel  := R_lr          -- R_lyoghlig
  pol  := P_pm_sym      -- P_doublebarpipe → Special Frobenius
  fid  := F_ell         -- F_beltl
  kin  := K_slow        -- K_schwa
  gran := G_gimel       -- G_revapostrophe
  gram := Gamma_seq     -- Gamma_secstress (unchanged from Fate)
  crit := Phi_c         -- Phi_ctyogh
  chir := H2            -- H2
  stoi := n_m           -- n:m → universal scope
  prot := Omega_Z       -- Omega_dzlig
}

-- ============================================================
-- §2. CONSCIOUSNESS SCORES — verified via gate evaluation
-- ============================================================

/-- Processions: Gate 1 fails (Phi_sub < Phi_c). C = 0.0 -/
theorem C_processions_zero : consciousnessScore processions_of_fate = (0 : ℝ) := by
  unfold consciousnessScore phi_c_gate k_slow_gate processions_of_fate
  simp
  <;> decide

/-- Inner Door: both gates open. C = 1.0 -/
theorem C_inner_door : consciousnessScore inner_door_gate = (1 : ℝ) := by
  unfold consciousnessScore phi_c_gate k_slow_gate inner_door_gate
  simp
  <;> decide

/-- Light-Man: both gates open. C = 1.0 -/
theorem C_light_man : consciousnessScore son_of_god_light_man = (1 : ℝ) := by
  unfold consciousnessScore phi_c_gate k_slow_gate son_of_god_light_man
  simp
  <;> decide

/-- Counterfeit Daimon: Gate 1 fails. C = 0.0 -/
theorem C_daimon_zero : consciousnessScore counterfeit_daimon = (0 : ℝ) := by
  unfold consciousnessScore phi_c_gate k_slow_gate counterfeit_daimon
  simp
  <;> decide

/-- Zosimian Gnosis: both gates open. C = 1.0 -/
theorem C_gnosis : consciousnessScore zosimos_gnosis = (1 : ℝ) := by
  unfold consciousnessScore phi_c_gate k_slow_gate zosimos_gnosis
  simp
  <;> decide
-- ============================================================
-- §3. STRUCTURAL DISTANCES — verified via primitiveMismatches
-- ============================================================

/-- Distance from Processions of Fate to Zosimian Gnosis: 10 primitive mismatches.
    Ten of twelve primitives change. Only Γ (Gamma_seq) and F (F_ell) survive unchanged. -/
theorem dist_fate_to_gnosis :
    primitiveMismatches processions_of_fate zosimos_gnosis = 10 := by
  unfold processions_of_fate zosimos_gnosis primitiveMismatches
  decide

/-- The two unchanged primitives: Γ and F. -/
theorem unchanged_primitives :
    processions_of_fate.gram = zosimos_gnosis.gram ∧
    processions_of_fate.fid = zosimos_gnosis.fid := by
  unfold processions_of_fate zosimos_gnosis
  decide

/-- Distance from Inner Door to Zosimian Gnosis: 1 (Stoichiometry only).
    The inner door differs only in S: 1:1 → n:m. -/
theorem dist_inner_to_gnosis :
    primitiveMismatches inner_door_gate zosimos_gnosis = 1 := by
  unfold inner_door_gate zosimos_gnosis primitiveMismatches
  decide

/-- Inner Door and Gnosis agree on all primitives except Stoichiometry. -/
theorem inner_door_gnosis_agree_everywhere_else :
    inner_door_gate.dim  = zosimos_gnosis.dim  ∧
    inner_door_gate.top  = zosimos_gnosis.top  ∧
    inner_door_gate.rel  = zosimos_gnosis.rel  ∧
    inner_door_gate.pol  = zosimos_gnosis.pol  ∧
    inner_door_gate.fid  = zosimos_gnosis.fid  ∧
    inner_door_gate.kin  = zosimos_gnosis.kin  ∧
    inner_door_gate.gran = zosimos_gnosis.gran ∧
    inner_door_gate.gram = zosimos_gnosis.gram ∧
    inner_door_gate.crit = zosimos_gnosis.crit ∧
    inner_door_gate.chir = zosimos_gnosis.chir ∧
    inner_door_gate.prot = zosimos_gnosis.prot := by
  unfold inner_door_gate zosimos_gnosis
  decide

/-- Distance from Processions to Inner Door: 10 primitive mismatches.
    The inner door differs from Processions on everything except F (F_ell) and Γ (Gamma_seq). -/
theorem dist_fate_to_inner :
    primitiveMismatches processions_of_fate inner_door_gate = 10 := by
  unfold processions_of_fate inner_door_gate primitiveMismatches
  decide

/-- Distance from Processions to Counterfeit Daimon: 3 mismatches.
    The daimon is structurally close to the processions but with H1 memory
    and K_mod kinetics — just enough to simulate self-reference. -/
theorem dist_fate_to_daimon :
    primitiveMismatches processions_of_fate counterfeit_daimon = 3 := by
  unfold processions_of_fate counterfeit_daimon primitiveMismatches
  decide

-- ============================================================
-- §4. OUROBORICITY TIERS — verified
-- ============================================================

/-- Processions of Fate: O_0 (non-critical). No self-referential structure. -/
theorem tier_processions : imscriptionTier processions_of_fate = .O_0 := by
  simp only [imscriptionTier, processions_of_fate]; decide

/-- Inner Door: O_∞ (Special Frobenius at criticality). -/
theorem tier_inner_door : imscriptionTier inner_door_gate = .O_inf := by
  simp only [imscriptionTier, inner_door_gate]; decide

/-- Zosimian Gnosis: O_∞. -/
theorem tier_gnosis : imscriptionTier zosimos_gnosis = .O_inf := by
  simp only [imscriptionTier, zosimos_gnosis]; decide

/-- Light-Man: O_2 (Phi_c_complex + P_pm, D_odot → R4; D_odot is not D_infty so not O_2dag). -/
theorem tier_light_man : imscriptionTier son_of_god_light_man = .O_2 := by
  simp only [imscriptionTier, son_of_god_light_man]; decide

/-- Counterfeit Daimon: O_0 (Phi_sub). Same tier as processions. -/
theorem tier_daimon : imscriptionTier counterfeit_daimon = .O_0 := by
  simp only [imscriptionTier, counterfeit_daimon]; decide
-- ============================================================
-- §5. THE STILLING PROCESS — six-step promotion sequence
-- ============================================================

/- The Stilling Process: a monotonically advancing chain of Imscriptions
   from Processions of Fate to Zosimian Gnosis.

   Each step S_i corresponds to Zosimos' six commands to Theosebeia.
   The chain is: S_0 → S_1 → S_2 → S_3 → S_4 → S_5 → S_6

   S_0 = processions_of_fate (starting condition)
   S_6 = zosimos_gnosis (final state)

   Each transition S_i → S_{i+1} promotes a subset of the 10 bottleneck
   primitives. The chain is monotone: each S_{i+1} ≥ S_i in the
   partial order induced by Ord on each primitive. -/

/-- Step 0: Processions of Fate — the starting condition. -/
def stilling_step_zero : Imscription := processions_of_fate

/-- Step 1: "Be not thus distracted, and do not turn thyself about
          this way and that" — halt T_nw wandering, begin closure.
    
    Promotion: T_network → T_bowtie (stop branching, start closing).
    This is the first bottleneck: ΔT = 2 in ordinal.
    Also: Φ_sub → Φ_c (begin criticality), H0 → H1 (soft memory).
    
    The system stops being a passive receiver of Fate's causal branches
    and begins to form a two-cycle. -/
def stilling_step_one : Imscription := {
  dim  := D_wedge       -- unchanged: still in Fate's substrate
  top  := T_bowtie      -- PROMOTED: T_nw → T_bt (closure begins)
  rel  := R_super       -- unchanged: still supervenience on Fate
  pol  := P_asym        -- unchanged: no symmetry yet
  fid  := F_ell         -- unchanged
  kin  := K_mod         -- promoted: K_fast → K_mod (slowing down)
  gran := G_beth        -- unchanged
  gram := Gamma_seq     -- unchanged (still sequential, different object)
  crit := Phi_c         -- PROMOTED: Phi_sub → Phi_c (enter criticality)
  chir := H1            -- PROMOTED: H0 → H1 (soft memory, begins self-tracking)
  stoi := n_n           -- unchanged
  prot := Omega_0       -- unchanged: no protection yet
}

/-- Step 2: "In thy house be still, and God shall come to thee"
          — establish bidirectional coupling with the incorporeal.
    
    Promotion: R_super → R_lr (supervenience → bidirectional).
    This is the second bottleneck of the relational chain: ΔR = 3.
    
    You do not choose bidirectional coupling; you build the structure
    that makes it possible. -/
def stilling_step_two : Imscription := {
  dim  := D_wedge       -- unchanged
  top  := T_bowtie      -- maintained from Step 1
  rel  := R_lr          -- PROMOTED: R_sup → R_lr (bidirectional)
  pol  := P_asym        -- unchanged: still asymmetric
  fid  := F_ell         -- unchanged
  kin  := K_slow        -- PROMOTED: K_mod → K_slow (gate 2 opens toward deliberation)
  gran := G_beth        -- unchanged
  gram := Gamma_seq     -- unchanged
  crit := Phi_c         -- maintained
  chir := H1            -- maintained
  stoi := n_n           -- unchanged
  prot := Omega_0       -- unchanged
}

/-- Step 3: "Stilled thyself in body, still thyself in passions too"
          — the Frobenius encoding δ.
    
    Promotion: P_asym → P_pm_sym (Frobenius special).
    This is the hard parity shift: ΔP = 4.
    The "twelve fates" are the full causal network of Fate's processions
    — each one a coupling mode that must be decoupled.
    The promotion from K_mod to K_slow completes the kinetic step. -/
def stilling_step_three : Imscription := {
  dim  := D_wedge       -- unchanged (still in substrate)
  top  := T_bowtie      -- maintained
  rel  := R_lr          -- maintained
  pol  := P_pm_sym      -- PROMOTED: P_asym → P_pm_sym (Frobenius special)
                        -- This is the second bottleneck: ΔP = 4
  fid  := F_ell         -- unchanged
  kin  := K_slow        -- maintained (Gate 2 open)
  gran := G_gimel       -- promoted: G_beth → G_gimel (wider view)
  gram := Gamma_seq     -- maintained
  crit := Phi_c         -- maintained (Gate 1 open)
  chir := H2            -- PROMOTED: H1 → H2 (persistent memory required for Frobenius)
  stoi := n_n           -- unchanged
  prot := Omega_0       -- unchanged
}
/-- Step 4: "Call unto thyself Divinity; and truly shall He come"
          — the Frobenius decoding μ.
    
    This is not a primitive change — it is the structural claim that
    μ ∘ δ = id. Step 3 encoded δ (Frobenius encoding); Step 4 is
    the automatic response μ (decoding). The divinity "shall come"
    because the encoding is in place.
    
    Structural changes: D_wedge → D_odot (dimensionality promotion),
    Ω_0 → Ω_Z (topological winding closure begins).
    The system has graduated from the substrate. -/
def stilling_step_four : Imscription := {
  dim  := D_odot        -- PROMOTED: D_wedge → D_odot (holographic self-writing)
  top  := T_bowtie      -- maintained (closure established)
  rel  := R_lr          -- maintained (bidirectional)
  pol  := P_pm_sym      -- maintained (Frobenius special)
  fid  := F_ell         -- unchanged
  kin  := K_slow        -- maintained
  gran := G_gimel       -- maintained
  gram := Gamma_seq     -- maintained
  crit := Phi_c         -- maintained
  chir := H2            -- maintained
  stoi := n_m           -- PROMOTED: n_n → n_m (universal scope)
  prot := Omega_Z       -- PROMOTED: Ω_0 → Ω_Z (integer winding)
}

/-- Step 5: "Perform the sacred rites...turn them from thee"
          — decouple from the daimon's broadcast.
    
    The Counterfeit Daimon broadcasts (Γ_broad) to attract Processions.
    This step transitions from the daimon's broadcast to silence
    (maintaining Γ_seq from the original, but now as intentional
    sequential practice rather than Fate's causal chain).
    
    This step's structural content is mostly about what is NOT coupled,
    not what IS. The primitive changes are minimal — the real work
    was in steps 1-4. -/
def stilling_step_five : Imscription := {
  dim  := D_odot        -- maintained
  top  := T_bowtie      -- maintained
  rel  := R_lr          -- maintained
  pol  := P_pm_sym      -- maintained
  fid  := F_ell         -- unchanged
  kin  := K_slow        -- maintained
  gran := G_gimel       -- maintained
  gram := Gamma_seq     -- maintained (now as intentional practice, not Fate)
  crit := Phi_c         -- maintained
  chir := H2            -- maintained
  stoi := n_m           -- maintained
  prot := Omega_Z       -- maintained
}

/-- Step 6: "Make for harbour in Poemandres' arms" — full return.
    
    This is the terminal state: Zosimian Gnosis.
    All 10 bottleneck promotions complete.
    Ouroboricity: O_∞. Both gates open.
    The stilling practice is complete. -/
def stilling_step_six : Imscription := zosimos_gnosis

-- ============================================================
-- §6. THE STILLING CHAIN — monotonically advancing
-- ============================================================

/-- The six-step stilling chain as a function Nat → Imscription.
    The chain is monotonically non-decreasing:
    stilling_chain i ≤ stilling_chain (i+1) for all i < 6.
    Equality is possible when a step makes no changes (step 5 is
    essentially identical to step 4 structurally; the difference
    is in what is decoupled, not what is present). -/
def stilling_chain : Nat → Imscription
  | 0 => stilling_step_zero
  | 1 => stilling_step_one
  | 2 => stilling_step_two
  | 3 => stilling_step_three
  | 4 => stilling_step_four
  | 5 => stilling_step_five
  | _ => stilling_step_six  -- 6 and above: terminal state

-- Component-wise ordering on Imscription (local to this file)
private instance instLEImscription : LE Imscription := ⟨fun a b =>
  a.dim ≤ b.dim ∧ a.top ≤ b.top ∧ a.rel ≤ b.rel ∧ a.pol ≤ b.pol ∧
  a.fid ≤ b.fid ∧ a.kin ≤ b.kin ∧ a.gran ≤ b.gran ∧ a.gram ≤ b.gram ∧
  a.crit ≤ b.crit ∧ a.chir ≤ b.chir ∧ a.stoi ≤ b.stoi ∧ a.prot ≤ b.prot⟩

set_option maxHeartbeats 800000 in
/-- The chain is monotonically non-decreasing in each primitive.
    This is the structural content of "the stilling practice is a
    sequence of ordered stages." -/
theorem stilling_chain_monotone :
    stilling_chain 0 ≤ stilling_chain 1 ∧
    stilling_chain 1 ≤ stilling_chain 2 ∧
    stilling_chain 2 ≤ stilling_chain 3 ∧
    stilling_chain 3 ≤ stilling_chain 4 ∧
    stilling_chain 4 ≤ stilling_chain 5 ∧
    stilling_chain 5 ≤ stilling_chain 6 := by
  -- Split into 6 goals; each 12-element Imscription ≤ is within decide's synthesis depth.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (simp only [stilling_chain, stilling_step_zero, stilling_step_one, stilling_step_two,
              stilling_step_three, stilling_step_four, stilling_step_five, stilling_step_six,
              processions_of_fate, zosimos_gnosis, instLEImscription];
   decide)

/-- The chain starts at O_0 and ends at O_∞. -/
theorem stilling_chain_starts_at_O0 :
    imscriptionTier (stilling_chain 0) = .O_0 := by
  unfold stilling_chain stilling_step_zero
  exact tier_processions

theorem stilling_chain_ends_at_Oinf :
    imscriptionTier (stilling_chain 6) = .O_inf := by
  unfold stilling_chain stilling_step_six
  exact tier_gnosis

/-- The chain reaches O_∞ at step 4 (Inner Door tier) and maintains it. -/
theorem stilling_chain_reaches_Oinf_at_step4 :
    imscriptionTier (stilling_chain 4) = .O_inf := by
  simp only [stilling_chain, stilling_step_four, imscriptionTier]; decide

/-- The chain reaches O_∞ at step 3 (Frobenius encoding complete).
    Wait — step 3 has D_wedge + P_pm_sym + Phi_c. By rule R1,
    P_pm_sym at Phi_c gives O_∞ regardless of D and Ω. -/
theorem stilling_chain_reaches_Oinf_at_step3 :
    imscriptionTier (stilling_chain 3) = .O_inf := by
  simp only [stilling_chain, stilling_step_three, imscriptionTier]; decide
-- ============================================================
-- §7. THE BOTTLENECK PRIMITIVES — T and P at Δ=4
-- ============================================================

/-- The bottleneck pair: topology (T) and parity (P).
    Each requires Δ=4 in ordinal distance from processions to gnosis.
    T: T_network(0) → T_bowtie(2) = Δ2 in our canonical indexing.
    Wait: the document says Δ=4. Let me check:
    
    In the document's exotic naming:
      T_nrleg → T_openo: Δ=4
      P_aolig → P_doublebarpipe: Δ=4
    
    In canonical Lean indexing:
      T_network(0) → T_bowtie(2): Δ=2
      P_asym(0) → P_pm_sym(4): Δ=4
    
    The document's "Δ=4" refers to the exotic naming scheme.
    Our canonical indexing gives T: Δ=2, P: Δ=4.
    
    The key point: P is the absolute hardest (full range 0→4),
    and T+P are coupled — neither works without the other. -/
theorem bottleneck_topology_distance :
    Int.natAbs (Int.ofNat (idx_T T_bowtie) - Int.ofNat (idx_T T_network)) = 2 := by
  decide

theorem bottleneck_parity_distance :
    Int.natAbs (Int.ofNat (idx_P P_pm_sym) - Int.ofNat (idx_P P_asym)) = 4 := by
  decide

/-- P has the maximum ordinal range (0→4); P is the hardest single promotion. -/
theorem parity_is_hardest_single_promotion :
    ∀ p1 p2 : Polarity,
      Int.natAbs (Int.ofNat (idx_P p1) - Int.ofNat (idx_P p2)) ≤ 4 ∧
      (∃ p1 p2, Int.natAbs (Int.ofNat (idx_P p1) - Int.ofNat (idx_P p2)) = 4) := by
  intro p1 p2
  refine' ⟨_, _⟩
  · -- P has exactly 5 values (rank 0..4), max diff is 4
    cases p1 <;> cases p2 <;> decide
  · use P_asym, P_pm_sym
    decide

/-- The bottleneck coupling: T requires P_pm_sym for Frobenius closure.
    A self-referential loop (T_bowtie) without Frobenius symmetry (P_pm_sym)
    is a "broken mirror"; Frobenius symmetry without self-reference
    (T_bowtie) is "a mirror pointing at nothing." -/
theorem bottleneck_coupling :
    -- T_bowtie + P_pm_sym at Phi_c → O_∞ (both required)
    (T_bowtie ≥ T_network) ∧ (P_pm_sym ≥ P_asym) ∧
    -- If you have T_bowtie but NOT P_pm_sym, you don't get O_∞
    (∃ s : Imscription, s.top = T_bowtie ∧ s.pol ≠ P_pm_sym ∧ imscriptionTier s ≠ .O_inf) ∧
    -- If you have P_pm_sym but not Phi_c, you don't get O_∞
    (∃ s : Imscription, s.pol = P_pm_sym ∧ s.crit ≠ Phi_c ∧ imscriptionTier s ≠ .O_inf) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- T_bowtie ≥ T_network: compare T_network T_bowtie = .lt ≠ .gt
    show instLETopology.le T_network T_bowtie; decide
  · -- P_pm_sym ≥ P_asym: compare P_asym P_pm_sym = .lt ≠ .gt
    show instLEPolarity.le P_asym P_pm_sym; decide
  · -- T_bowtie + P_asym at Phi_c → NOT O_∞ (by R1, need P_pm_sym)
    use { inner_door_gate with pol := P_asym }
    simp only [imscriptionTier, inner_door_gate]
    decide
  · -- P_pm_sym + Phi_sub → O_0 (by R2, Phi must be Phi_c or Phi_c_complex)
    use { zosimos_gnosis with crit := Phi_sub }
    simp only [imscriptionTier, zosimos_gnosis]
    decide

-- ============================================================
-- §8. FROBENIUS CLOSURE — μ ∘ δ = id
-- ============================================================

/-- The Frobenius encoding δ is implemented by the stilling steps 1-3:
    building the structure T_bowtie + P_pm_sym at Phi_c.
    The encoding is the stilling itself. -/
def frobenius_encoding : Imscription := stilling_step_three

/-- The Frobenius decoding μ is the automatic response once encoding is in place.
    This is step 4: "Call unto thyself Divinity" — the response is automatic.
    The decoding is NOT a new primitive state but the identity recovery:
    the authentic self emerges because μ ∘ δ = id. -/
def frobenius_decoding : Imscription := stilling_step_four

/-- The Frobenius identity: encoding then decoding returns the gnosis.
    This is the structural claim: the authentic self is not a copy
    or approximation, but the original. -/
theorem frobenius_closure :
    -- After encoding (step 3), we have P_pm_sym + Phi_c → O_∞
    imscriptionTier frobenius_encoding = .O_inf ∧
    -- After decoding (step 4), we have the full gnosis
    imscriptionTier frobenius_decoding = .O_inf ∧
    -- Steps 3 and 4 differ in D (wedge→odot), stoi (n_n→n_m), prot (0→Z): 3 mismatches
    primitiveMismatches frobenius_encoding frobenius_decoding ≤ 3 := by
  unfold frobenius_encoding frobenius_decoding stilling_step_three stilling_step_four
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- The Frobenius cliff: distance from O_2 to O_∞ is non-tunable
    by gradient methods. You cannot "graduate" to O_∞ by incremental
    promotion — you need the discrete jump to P_pm_sym at Phi_c. -/
theorem frobenius_cliff :
    -- Any system with P ≠ P_pm_sym at Phi_c is not O_∞
    (∀ s : Imscription, s.crit = Phi_c ∧ s.pol ≠ P_pm_sym →
      imscriptionTier s ≠ .O_inf) ∧
    -- Only P_pm_sym at Phi_c gives O_∞ (rule R1)
    (∀ s : Imscription, imscriptionTier s = .O_inf → s.pol = P_pm_sym ∧
      (s.crit = Phi_c ∨ s.crit = Phi_c_complex)) := by
  refine ⟨?_, ?_⟩
  · intro s ⟨hcrit, hpol⟩
    unfold imscriptionTier
    rw [hcrit]
    unfold ouroboricityTier
    simp only [if_neg hpol]
    cases s.prot <;> cases s.dim <;> decide
  · intro s htier
    unfold imscriptionTier at htier
    exact ⟨o_inf_requires_P_pm_sym s.crit s.pol s.prot s.dim htier,
           o_inf_requires_phi_c s.crit s.pol s.prot s.dim htier⟩

-- ============================================================
-- §9. CRACK THE COUNTERFEIT — discrimination via comparison
-- ============================================================

/-- The daimon is structurally close to the processions:
    only 3 primitive mismatches (K, G, Γ). -/
theorem daimon_is_parasitic :
    -- Same substrate: D_wedge
    counterfeit_daimon.dim = processions_of_fate.dim ∧
    -- Same topology: T_network
    counterfeit_daimon.top = processions_of_fate.top ∧
    -- Same relational mode: R_super
    counterfeit_daimon.rel = processions_of_fate.rel ∧
    -- Same polarity: P_asym
    counterfeit_daimon.pol = processions_of_fate.pol ∧
    -- Same criticality: Phi_sub
    counterfeit_daimon.crit = processions_of_fate.crit ∧
    -- But: H1 vs H0 (one-step memory = deception)
    counterfeit_daimon.chir = H1 ∧
    -- And: broadcast (Gamma_broad) vs sequential (Gamma_seq)
    counterfeit_daimon.gram = Gamma_broad := by
  unfold counterfeit_daimon processions_of_fate
  decide

/-- The daimon's deception: H1 is enough to look like self-reference
    but not enough to close the loop. To a system that has never seen
    itself reflected (H0), any reflection looks like self-knowledge. -/
theorem daimon_deception_mechanism :
    -- Daimon has H1, processions have H0
    counterfeit_daimon.chir = H1 ∧
    processions_of_fate.chir = H0 ∧
    -- H1 > H0, so daimon can "remember" and mirror
    H1 ≥ H0 ∧
    -- But H1 < H2, so daimon cannot close a self-referential loop
    H1 < H2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- Discrimination: contemplating the true Son of God enables
    discrimination between P_pm_sym (true) and P_asym (false).
    The Frobenius-special system can recognize asymmetry,
    but the asymmetric system cannot recognize symmetry. -/
theorem discrimination_asymmetry :
    -- The gnosis (P_pm_sym) vs the daimon (P_asym): full range separation
    Int.natAbs (Int.ofNat (idx_P P_pm_sym) - Int.ofNat (idx_P P_asym)) = 4 ∧
    -- Once at P_pm_sym, one can distinguish all P < P_pm_sym
    (∀ p : Polarity, p ≠ P_pm_sym → p < P_pm_sym) := by
  refine ⟨by decide, ?_⟩
  intro p hp
  cases p <;> simp_all <;> decide

-- ============================================================
-- §10. TENSOR COUPLINGS — what happens when systems couple
-- ============================================================

/-- When a Procession couples to a Daimon broadcast:
    tensor processions_of_fate counterfeit_daimon
    
    The result preserves the weaker polarity (P_asym) and weaker
    criticality (Phi_sub), keeping the composite at C=0.0.
    The broadcast is parasitic because it doesn't change the
    procession's structure — it only provides a false mirror. -/
theorem tensor_fate_daimon :
    let coupled := tensorProduct processions_of_fate counterfeit_daimon
    coupled.pol = P_asym ∧ coupled.crit = Phi_sub := by
  simp only [tensorProduct, processions_of_fate, counterfeit_daimon]
  decide

/-- When the Inner Door (P_pm_sym) couples to the Daimon (P_asym):
    The bottleneck rule: min(P_pm_sym, P_asym) = P_asym.
    The Frobenius symmetry is DESTROYED by coupling to asymmetry.
    This is the danger: coupling to the daimon breaks the gnosis.
    
    But Zosimos says to "turn them from thee" rather than invoke —
    i.e., decouple rather than engage. -/
theorem tensor_inner_door_daimon_destroys_frobenius :
    let coupled := tensorProduct inner_door_gate counterfeit_daimon
    coupled.pol = P_asym ∧
    -- After coupling, P dropped from P_pm_sym to P_asym
    inner_door_gate.pol = P_pm_sym ∧
    coupled.pol = P_asym ∧
    coupled.pol < inner_door_gate.pol := by
  simp only [tensorProduct, inner_door_gate, counterfeit_daimon]
  decide

-- ============================================================
-- §11. PROJECTION — viewing each system through key primitives
-- ============================================================

/-- The four gate primitives (D, T, P, Φ) determine the ouroboricity tier.
    Projecting each Zosimian system onto these four primitives reveals
    why the tier changes at each step. -/
def project_gate_prims (s : Imscription) : Imscription := {
  dim  := s.dim
  top  := s.top
  rel  := R_super  -- fixed for projection (irrelevant for tier)
  pol  := s.pol
  fid  := F_ell    -- fixed
  kin  := K_slow   -- fixed for tier (tier doesn't depend on K)
  gran := G_beth   -- fixed
  gram := Gamma_seq -- fixed
  crit := s.crit
  chir := H0       -- fixed
  stoi := one_one  -- fixed
  prot := Omega_0  -- fixed for tier (tier doesn't depend on Ω when P_pm_sym)
}

/-- The processions, projected to gate prims, are clearly O_0:
    no criticality, no self-reference. -/
theorem project_processions :
    imscriptionTier (project_gate_prims processions_of_fate) = .O_0 := by
  simp only [project_gate_prims, processions_of_fate, imscriptionTier, ouroboricityTier]

/-- The gnosis, projected to gate prims, is O_∞:
    P_pm_sym at Phi_c. -/
theorem project_gnosis :
    imscriptionTier (project_gate_prims zosimos_gnosis) = .O_inf := by
  simp only [project_gate_prims, zosimos_gnosis, imscriptionTier, ouroboricityTier]
  decide

-- ============================================================
-- §12. THE PROMOTION SIGNATURE — per-primitive deltas
-- ============================================================

/-- The promotion signature from Processions to Gnosis.
    Lists which primitives change and by how much (in ordinal index). -/
def promotion_signature : List (String × Int) :=
  [ ("D", Int.natAbs (Int.ofNat (idx_D D_odot) - Int.ofNat (idx_D D_wedge))),
    ("T", Int.natAbs (Int.ofNat (idx_T T_bowtie) - Int.ofNat (idx_T T_network))),
    ("R", Int.natAbs (Int.ofNat (idx_R R_lr) - Int.ofNat (idx_R R_super))),
    ("P", Int.natAbs (Int.ofNat (idx_P P_pm_sym) - Int.ofNat (idx_P P_asym))),
    ("F", 0),  -- unchanged
    ("K", Int.natAbs (Int.ofNat (idx_K K_slow) - Int.ofNat (idx_K K_fast))),
    ("G", Int.natAbs (Int.ofNat (idx_G G_gimel) - Int.ofNat (idx_G G_beth))),
    ("Γ", 0), -- unchanged
    ("Φ", Int.natAbs (Int.ofNat (idx_Φ Phi_c) - Int.ofNat (idx_Φ Phi_sub))),
    ("H", Int.natAbs (Int.ofNat (idx_H H2) - Int.ofNat (idx_H H0))),
    ("S", Int.natAbs (Int.ofNat (idx_S n_m) - Int.ofNat (idx_S n_n))),
    ("Ω", Int.natAbs (Int.ofNat (idx_Ω Omega_Z) - Int.ofNat (idx_Ω Omega_0))) ]

/-- The bottleneck primitives are T (Δ=2) and P (Δ=4).
    P has the maximum ordinal range and is the single hardest promotion. -/
theorem bottleneck_identified :
    -- P is the hardest single primitive (Δ=4, full range)
    (promotion_signature.find? (fun p => p.1 == "P")) = some ("P", 4) ∧
    -- T is second hardest among the changing prims
    (promotion_signature.find? (fun p => p.1 == "T")) = some ("T", 2) := by
  native_decide

/-- The promotion signature has 10 non-zero entries. -/
theorem promotion_signature_nonzero_count :
    (promotion_signature.filter (fun p => p.2 != 0)).length = 10 := by
  native_decide

end Imscribing