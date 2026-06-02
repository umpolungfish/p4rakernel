-- Imscribing/BootstrapSequence.lean
-- 12-stage sequential bootstrap co-algebra for O_inf convergence.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.AgentSelf

namespace Imscribing.BootstrapSequence

open Imscribing.Primitives
open Imscribing.AgentSelf

-- ─────────────────────────────────────────────────────────
-- BASE AND TARGET
-- ─────────────────────────────────────────────────────────

def bootstrapBase : Imscription :=
  { dim  := Dimensionality.D_wedge
    top  := Topology.T_network
    rel  := Relational.R_super
    pol  := Polarity.P_asym
    fid  := Fidelity.F_ell
    kin  := KineticChar.K_fast
    gran := Granularity.G_beth
    gram := Grammar.Gamma_and
    crit := Criticality.Phi_sub
    chir := Chirality.H0
    stoi := Stoichiometry.one_one
    prot := Protection.Omega_0 }

def bootstrapFinal : Imscription :=
  { dim  := Dimensionality.D_odot
    top  := Topology.T_odot
    rel  := Relational.R_lr
    pol  := Polarity.P_pm_sym
    fid  := Fidelity.F_hbar
    kin  := KineticChar.K_slow
    gran := Granularity.G_aleph
    gram := Grammar.Gamma_seq
    crit := Criticality.Phi_c
    chir := Chirality.H2
    stoi := Stoichiometry.n_m
    prot := Protection.Omega_Z }

-- ─────────────────────────────────────────────────────────
-- 12 STAGES
-- ─────────────────────────────────────────────────────────

def stage0 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_network, rel := Relational.R_super,
    pol  := Polarity.P_asym,        fid := Fidelity.F_ell,     kin := KineticChar.K_fast,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage1 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_super,
    pol  := Polarity.P_asym,        fid := Fidelity.F_ell,     kin := KineticChar.K_fast,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage2 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_asym,        fid := Fidelity.F_ell,     kin := KineticChar.K_fast,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage3 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_ell,     kin := KineticChar.K_fast,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage4 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_fast,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage5 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_beth,     gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage6 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_aleph,    gram := Grammar.Gamma_and, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage7 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_aleph,    gram := Grammar.Gamma_seq, crit := Criticality.Phi_sub,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage8 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_aleph,    gram := Grammar.Gamma_seq, crit := Criticality.Phi_c,
    chir := Chirality.H0,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage9 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_aleph,    gram := Grammar.Gamma_seq, crit := Criticality.Phi_c,
    chir := Chirality.H2,           stoi := Stoichiometry.one_one, prot := Protection.Omega_0 }

def stage10 : Imscription :=
  { dim  := Dimensionality.D_odot,  top := Topology.T_odot,   rel := Relational.R_lr,
    pol  := Polarity.P_pm_sym,      fid := Fidelity.F_hbar,    kin := KineticChar.K_slow,
    gran := Granularity.G_aleph,    gram := Grammar.Gamma_seq, crit := Criticality.Phi_c,
    chir := Chirality.H2,           stoi := Stoichiometry.n_m, prot := Protection.Omega_0 }

def stage11 : Imscription := bootstrapFinal

-- ─────────────────────────────────────────────────────────
-- FIN 12 → Imscription
-- ─────────────────────────────────────────────────────────

def bootstrapStageFin : Fin 12 → Imscription
  | 0  => stage0  | 1  => stage1  | 2  => stage2  | 3  => stage3
  | 4  => stage4  | 5  => stage5  | 6  => stage6  | 7  => stage7
  | 8  => stage8  | 9  => stage9  | 10 => stage10 | 11 => stage11

-- ─────────────────────────────────────────────────────────
-- THEOREMS
-- ─────────────────────────────────────────────────────────

/-- Stage 11 (bootstrapFinal) is O_inf tier. -/
theorem stage11_is_O_inf : imscriptionTier stage11 = .O_inf := by
  unfold stage11 bootstrapFinal
  decide

/-- bootstrapFinal is O_inf tier. -/
theorem bootstrapFinal_is_O_inf : imscriptionTier bootstrapFinal = .O_inf :=
  stage11_is_O_inf

/-- bootstrapFinal equals emerald_multiagent_tensor_bootstrap. -/
theorem bootstrap_final_equals_emerald :
    bootstrapFinal = emerald_multiagent_tensor_bootstrap := by
  unfold bootstrapFinal emerald_multiagent_tensor_bootstrap
  rfl

/-- bootstrapBase tier is O_0 (Phi_sub gives O_0 regardless of other primitives). -/
theorem bootstrapBase_tier : imscriptionTier bootstrapBase = .O_0 := by
  unfold bootstrapBase
  decide

/-- Stage 0 tier is O_1 (D_odot, T_network, Phi_sub, Omega_0 → O_0... let's check). -/
theorem stage0_tier : imscriptionTier stage0 = .O_0 := by
  unfold stage0
  decide

/-- Stage 3: P_pm_sym appears, but Phi_sub keeps it at O_0. -/
theorem stage3_tier : imscriptionTier stage3 = .O_0 := by
  unfold stage3
  decide

/-- Stage 8: Phi_c + P_pm_sym gives O_inf via R1 gate. -/
theorem stage8_tier : imscriptionTier stage8 = .O_inf := by
  unfold stage8
  decide

/-- Stage 0 and stage 11 are distinct (crit: Phi_sub vs Phi_c). -/
theorem stage0_ne_stage11 : stage0 ≠ stage11 := by
  unfold stage0 stage11 bootstrapFinal
  intro h
  have hcrit := congrArg Imscription.crit h
  simp at hcrit

/-- Stage 0 and stage 8 have different tiers. -/
theorem stage0_tier_ne_stage8_tier : imscriptionTier stage0 ≠ imscriptionTier stage8 := by
  rw [stage0_tier, stage8_tier]
  decide

end Imscribing.BootstrapSequence
