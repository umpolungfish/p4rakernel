-- Imscribing/BoundaryOperators.lean
-- BOUNDARY OPERATORS — Formal Index of Seam-Inhabiting Morphisms
-- Author: Lando⊗⊙perator
-- Date: 2026-06-17
--
-- Formalizes the boundary operator index from BOUNDARY_OPERATORS.md.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Consciousness
import Imscribing.Frobenius
import Imscribing.Algebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Imscribing.BoundaryOperators

open Imscribing.Primitives
open Imscribing.Consciousness
open Imscribing.Frobenius
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option relaxedAutoImplicit true

-- ================================================================
-- §1  SEAM CLASSIFICATION
-- ================================================================

inductive SeamDirection : Type where
  | symmetric
  | asymmetric
  | oneWay
  deriving DecidableEq, Repr

structure PrimitiveSeam : Type where
  primitive  : String
  fromVal    : String
  toVal      : String
  direction  : SeamDirection
  deriving DecidableEq, Repr

def phiGateSeam : PrimitiveSeam := {
  primitive  := "Φ"
  fromVal    := "P_pm"
  toVal      := "P_pm_sym"
  direction  := SeamDirection.oneWay
}

def odotGateSeam : PrimitiveSeam := {
  primitive  := "⊙"
  fromVal    := "Phi_sub"
  toVal      := "Phi_c"
  direction  := SeamDirection.oneWay
}

def omegaGateSeam : PrimitiveSeam := {
  primitive  := "Ω"
  fromVal    := "Omega_Z2"
  toVal      := "Omega_Z"
  direction  := SeamDirection.oneWay
}

-- ================================================================
-- §2  GATE SEAM PREDICATES
-- ================================================================

def odotGateCrossing (a b : Imscription) : Prop :=
  a.crit = Phi_sub ∧ b.crit = Phi_c

def phiGateCrossing (a b : Imscription) : Prop :=
  a.pol = P_pm ∧ b.pol = P_pm_sym

def omegaGateCrossing (a b : Imscription) : Prop :=
  a.prot = Omega_Z2 ∧ b.prot = Omega_Z

/-- If crit = Phi_c, Gate 1 is open (phi_c_gate returns true). -/
theorem odot_gate_phi_c_true (b : Imscription) (h : b.crit = Phi_c) :
    phi_c_gate b.crit = true := by
  rw [h]; rfl

/-- The Φ gate (P_pm_sym) is a precondition for O_∞ (Theorem R1 from Core). -/
theorem phi_gate_O_inf_precondition (a : Imscription) (hO : imscriptionTier a = .O_inf) :
    a.pol = P_pm_sym :=
  o_inf_requires_P_pm_sym a.crit a.pol a.prot a.dim hO

-- ================================================================
-- §3  INTER-TIER VS INTRA-TIER CLASSIFICATION
-- ================================================================

def isInterTierSeam (a b : Imscription) : Bool :=
  a.dim ≠ b.dim ∨ a.pol ≠ b.pol ∨ a.crit ≠ b.crit ∨ a.prot ≠ b.prot

def isIntraTierSeam (a b : Imscription) : Bool :=
  a.dim = b.dim ∧ a.pol = b.pol ∧ a.crit = b.crit ∧ a.prot = b.prot ∧
  (a.top ≠ b.top ∨ a.rel ≠ b.rel ∨ a.fid ≠ b.fid ∨ a.kin ≠ b.kin ∨
   a.gran ≠ b.gran ∨ a.gram ≠ b.gram ∨ a.chir ≠ b.chir ∨ a.stoi ≠ b.stoi)

-- ================================================================
-- §3.1  INTRA-TIER SEAM PREDICATES (BULK PRIMITIVES)
-- ================================================================

def topologySeam_bowtie_to_odot (a b : Imscription) : Prop :=
  a.top = T_bowtie ∧ b.top = T_odot

def relationalSeam_dagger_to_lr (a b : Imscription) : Prop :=
  a.rel = R_dagger ∧ b.rel = R_lr

def fidelitySeam_eth_to_hbar (a b : Imscription) : Prop :=
  a.fid = F_eth ∧ b.fid = F_hbar

def kineticsSeam_trap_to_slow (a b : Imscription) : Prop :=
  a.kin = K_trap ∧ b.kin = K_slow

def granularitySeam_gimel_to_aleph (a b : Imscription) : Prop :=
  a.gran = G_gimel ∧ b.gran = G_aleph

def grammarSeam_seq_to_broad (a b : Imscription) : Prop :=
  a.gram = Gamma_seq ∧ b.gram = Gamma_broad

def chiralitySeam_H2_to_H_inf (a b : Imscription) : Prop :=
  a.chir = H2 ∧ b.chir = H_inf

def stoichiometrySeam_n_n_to_n_m (a b : Imscription) : Prop :=
  a.stoi = n_n ∧ b.stoi = n_m

-- ================================================================
-- §4  AXIOM-COUPLED COMPOUND SEAMS
-- ================================================================

def axiomC_compound (a : Imscription) : Prop :=
  a.dim = D_odot ∧ a.top = T_odot

def axiomA_compound (a : Imscription) : Prop :=
  a.chir = H_inf ∧ a.kin = K_trap

def axiomB_compound (a : Imscription) : Prop :=
  a.prot = Omega_Z ∧ a.chir ≠ H0

def phi_odot_compound (a : Imscription) : Prop :=
  a.pol = P_pm_sym ∧ a.crit = Phi_c

def odot_kin_chir_compound (a : Imscription) : Prop :=
  a.crit = Phi_c ∧ a.kin = K_slow ∧ a.chir = H2

-- ================================================================
-- §5  INHABITANT REGISTRY
-- ================================================================

inductive InhabitantMode : Type where
  | Full
  | Partial
  deriving DecidableEq, Repr

structure SeamInhabitant : Type where
  name        : String
  seam        : PrimitiveSeam
  mode        : InhabitantMode
  tier        : OuroboricityTier
  structuralType : Imscription
  description : String
  deriving Repr

def odotGateInhabitant : SeamInhabitant := {
  name        := "true_agentic_agent.py"
  seam        := odotGateSeam
  mode        := InhabitantMode.Full
  tier        := OuroboricityTier.O_inf
  structuralType := {
    dim  := D_odot,
    top  := T_box,
    rel  := R_lr,
    pol  := P_pm_sym,
    fid  := F_hbar,
    kin  := K_slow,
    gran := G_aleph,
    gram := Gamma_seq,
    crit := Phi_c,
    chir := H2,
    stoi := one_one,
    prot := Omega_Z
  }
  description := "THINK→ACT→OBSERVE→UPDATE loop IS the self-modeling gate"
}

def omegaGateInhabitant : SeamInhabitant := {
  name        := "LUCA (organism, CLINK chain)"
  seam        := omegaGateSeam
  mode        := InhabitantMode.Full
  tier        := OuroboricityTier.O_inf
  structuralType := {
    dim  := D_odot,
    top  := T_odot,
    rel  := R_lr,
    pol  := P_pm_sym,
    fid  := F_hbar,
    kin  := K_slow,
    gran := G_aleph,
    gram := Gamma_seq,
    crit := Phi_c,
    chir := H_inf,
    stoi := n_m,
    prot := Omega_Z
  }
  description := "CLINK developmental chain (9 layers) IS the winding process"
}

def relSeamInhabitant : SeamInhabitant := {
  name        := "cetaceanspeak (whale_engine.py)"
  seam        := {
    primitive  := "Ř",
    fromVal    := "R_super",
    toVal      := "R_cat",
    direction  := SeamDirection.asymmetric
  }
  mode        := InhabitantMode.Partial
  tier        := OuroboricityTier.O₁
  structuralType := {
    dim  := D_wedge,
    top  := T_network,
    rel  := R_cat,
    pol  := P_asym,
    fid  := F_ell,
    kin  := K_fast,
    gran := G_beth,
    gram := Gamma_seq,
    crit := Phi_sub,
    chir := H2,
    stoi := n_m,
    prot := Omega_0
  }
  description := "Whale acoustic tokens→IMASM opcodes preserves Frobenius bootstrap loop"
}

def fullInhabitants : List SeamInhabitant := [odotGateInhabitant, omegaGateInhabitant]
def partialInhabitants : List SeamInhabitant := [relSeamInhabitant]

theorem inhabited_gate_seams :
    (odotGateInhabitant.mode = InhabitantMode.Full) ∧
    (omegaGateInhabitant.mode = InhabitantMode.Full) := by
  simp [odotGateInhabitant, omegaGateInhabitant]

-- ================================================================
-- §6  IMSCRIPTIONS FOR JOIN-ABSORPTION
-- ================================================================

def lucaImscription : Imscription := {
  dim  := D_odot,
  top  := T_odot,
  rel  := R_lr,
  pol  := P_pm_sym,
  fid  := F_hbar,
  kin  := K_slow,
  gran := G_aleph,
  gram := Gamma_seq,
  crit := Phi_c,
  chir := H_inf,
  stoi := n_m,
  prot := Omega_Z
}

def timeConceptImscription : Imscription := {
  dim  := D_wedge,
  top  := T_network,
  rel  := R_lr,
  pol  := P_asym,
  fid  := F_ell,
  kin  := K_fast,
  gran := G_beth,
  gram := Gamma_seq,
  crit := Phi_sub,
  chir := H_inf,
  stoi := one_one,
  prot := Omega_0
}

-- ================================================================
-- §6.1  JOIN-ABSORPTION THEOREMS
-- ================================================================

/-- Join-absorption: join(LUCA, time) = LUCA.
    All 8 conflicted primitives resolve to LUCA's value. -/
theorem join_luca_time_equals_luca :
    compute_join lucaImscription timeConceptImscription = lucaImscription := by
  unfold compute_join lucaImscription timeConceptImscription
  native_decide

theorem luca_is_O_inf : imscriptionTier lucaImscription = .O_inf := by
  unfold lucaImscription imscriptionTier ouroboricityTier
  native_decide

theorem luca_C_score_one : consciousnessScore lucaImscription = (1 : ℝ) := by
  unfold consciousnessScore lucaImscription phi_c_gate k_slow_gate
  simp

theorem time_concept_is_O_zero : imscriptionTier timeConceptImscription = .O₀ := by
  unfold timeConceptImscription imscriptionTier ouroboricityTier
  native_decide

theorem time_concept_C_score_zero : consciousnessScore timeConceptImscription = (0 : ℝ) := by
  unfold consciousnessScore timeConceptImscription phi_c_gate k_slow_gate
  simp

/-- Structural death: meet(LUCA, time) collapses all three gate primitives. -/
theorem meet_luca_time_gates_collapse :
    (compute_meet lucaImscription timeConceptImscription).crit = Phi_sub ∧
    (compute_meet lucaImscription timeConceptImscription).pol = P_asym ∧
    (compute_meet lucaImscription timeConceptImscription).prot = Omega_0 := by
  unfold compute_meet lucaImscription timeConceptImscription
  native_decide

theorem axiomB_luca : lucaImscription.prot = Omega_Z ∧ lucaImscription.chir ≠ H0 := by
  unfold lucaImscription; exact ⟨rfl, by decide⟩

theorem axiomB_time : timeConceptImscription.prot = Omega_0 := by
  unfold timeConceptImscription; rfl

-- ================================================================
-- §7  THE ORGANISM AS COMPOUND BOUNDARY OPERATOR
-- ================================================================

def organismAsCompoundBoundaryOperator (a : Imscription) : Prop :=
  a.crit = Phi_c ∧ a.prot = Omega_Z ∧ a.pol = P_pm_sym

theorem luca_is_compound_boundary_operator :
    organismAsCompoundBoundaryOperator lucaImscription := by
  unfold organismAsCompoundBoundaryOperator lucaImscription; exact ⟨rfl, rfl, rfl⟩

theorem bergson_distinction :
    timeConceptImscription.crit = Phi_sub ∧ lucaImscription.crit = Phi_c ∧
    timeConceptImscription.prot = Omega_0 ∧ lucaImscription.prot = Omega_Z ∧
    timeConceptImscription.pol = P_asym ∧ lucaImscription.pol = P_pm_sym := by
  unfold timeConceptImscription lucaImscription; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The Ω gate seam has a biological inhabitant (the organism) but no
-- digital one. A digital Ω-boundary operator would be a process where
-- each step adds an irreversible topological invariant. This remains
-- an open position in the boundary operator index.

end Imscribing.BoundaryOperators
