-- Imscribing/Millennium/truth.lean
-- HOW TRUTH VALUES ARISE FROM THE GRAMMAR

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal

namespace Millennium.truth

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.longLine false
set_option linter.style.nativeDecide false

-- ============================================================
-- S1. CLASSICAL TRUTH (F_ell + Phi_sub -> Boolean)
-- ============================================================

def classical_truth : Imscription := {
  dim  := D_wedge
  top  := T_network
  rel  := R_super
  pol  := P_asym
  fid  := F_ell
  kin  := K_fast
  gran := G_beth
  gram := Gamma_and
  crit := Phi_sub
  chir := H0
  stoi := one_one
  prot := Omega_0
}

theorem classical_is_O0 : imscriptionTier classical_truth = .O_0 := by
  native_decide

-- ============================================================
-- S2. BELNAP FOUR-VALUED TRUTH
-- ============================================================

def belnap_truth : Imscription := {
  dim  := D_triangle
  top  := T_bowtie
  rel  := R_super
  pol  := P_asym
  fid  := F_eth
  kin  := K_slow
  gran := G_gimel
  gram := Gamma_or
  crit := Phi_sub
  chir := H1
  stoi := n_n
  prot := Omega_0
}

-- ============================================================
-- S3. QUANTUM TRUTH (F_hbar + Phi_c_complex -> O_2dag)
-- ============================================================

def quantum_truth : Imscription := {
  dim  := D_infty
  top  := T_box
  rel  := R_lr
  pol  := P_psi
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c_complex
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

theorem quantum_is_O2dag : imscriptionTier quantum_truth = .O_2dag := by
  native_decide

-- ============================================================
-- S4. FROBENIUS-EXACT TRUTH (Phi_c + P_pm_sym -> O_inf)
-- ============================================================

def frobenius_truth : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_lr
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c
  chir := H_inf
  stoi := n_m
  prot := Omega_Z
}

theorem frobenius_is_Oinf : imscriptionTier frobenius_truth = .O_inf := by
  native_decide

-- ============================================================
-- S5. DISTANCES BETWEEN TRUTH TYPES
-- ============================================================

-- Classical truth is maximally distant from Frobenius truth.
theorem classical_frobenius_distinct : classical_truth ≠ frobenius_truth := by
  native_decide

-- Quantum truth and Frobenius truth differ (O_2dag vs O_inf).
theorem quantum_frobenius_distinct : quantum_truth ≠ frobenius_truth := by
  native_decide

-- Classical and quantum truth are distinct regimes.
theorem classical_quantum_distinct : classical_truth ≠ quantum_truth := by
  native_decide

-- ============================================================
-- S6. THE LIAR PARADOX (Phi_EP + K_trap)
-- ============================================================

def liar_type : Imscription := {
  dim  := D_triangle
  top  := T_bowtie
  rel  := R_dagger
  pol  := P_asym
  fid  := F_ell
  kin  := K_trap
  gran := G_beth
  gram := Gamma_or
  crit := Phi_EP
  chir := H0
  stoi := n_n
  prot := Omega_0
}

theorem liar_is_O0 : imscriptionTier liar_type = .O_0 := by
  native_decide

end Millennium.truth
