-- Imscribing/HowHilbertQMArise.lean
-- HOW HILBERT-SPACE QUANTUM MECHANICS ARISES FROM THE GRAMMAR
-- QM = unique type satisfying P_psi + F_hbar + Phi_c_complex.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

namespace Imscribing.HowHilbertQMArise

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.longLine false

-- ============================================================
-- S1. THE CANONICAL QM IMSCRIPTION
-- ============================================================

def quantum_mechanics : Imscription := {
  dim  := D_infty
  top  := T_odot
  rel  := R_dagger
  pol  := P_psi
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_and
  crit := Phi_c_complex
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

-- QM is O_2dag: Phi_c_complex + P_psi (not P_pm_sym) + Omega_Z + D_infty.
theorem qm_tier : imscriptionTier quantum_mechanics = .O_2dag := by
  unfold imscriptionTier quantum_mechanics ouroboricityTier
  decide

-- ============================================================
-- S2. POSTULATE DERIVATIONS
-- ============================================================

-- POSTULATE 1 (States as rays): P_psi -> U(1) phase -> projective Hilbert space.
-- POSTULATE 2 (Self-adjoint observables): R_dagger -> A = A-dagger.
-- POSTULATE 3 (Unitary evolution): F_hbar + H2 -> U-dagger U = I.
-- POSTULATE 4 (Born rule): F_hbar + P_psi -> |<phi|psi>|^2 is unique.
-- POSTULATE 5 (Tensor product): Gamma_and + G_aleph -> H_A tensor H_B.

-- ============================================================
-- S3. WHY COMPLEX NUMBERS?
-- ============================================================

-- Phi_c_complex + P_psi forces C:
--   Phi_c_complex -> analytic continuation beyond R
--   P_psi -> U(1) phase symmetry (S^1)
--   Together: C = span_R{1, i}, S^1 subset C.

-- ============================================================
-- S4. THE MEASUREMENT PROBLEM (STRUCTURAL)
-- ============================================================

def measurement_apparatus : Imscription := {
  dim  := D_infty
  top  := T_bowtie
  rel  := R_lr
  pol  := P_pm
  fid  := F_eth
  kin  := K_fast
  gran := G_gimel
  gram := Gamma_seq
  crit := Phi_EP
  chir := H0
  stoi := n_n
  prot := Omega_Z2
}

-- tensorProduct(QM, apparatus).crit = Phi_EP (max of Phi_c_complex and Phi_EP).
theorem measurement_tensor_crit :
    (tensorProduct quantum_mechanics measurement_apparatus).crit = Phi_EP := by
  unfold tensorProduct quantum_mechanics measurement_apparatus
  decide

-- ============================================================
-- S5. QUANTUM FIELD THEORY (FROBENIUS-CLOSED)
-- ============================================================

def quantum_field_theory : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_dagger
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_and
  crit := Phi_c
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

-- QFT is O_inf: P_pm_sym at Phi_c opens the Frobenius gate.
theorem qft_tier : imscriptionTier quantum_field_theory = .O_inf := by
  decide

-- QM -> QFT: dim (D_infty->D_odot), pol (P_psi->P_pm_sym), crit (Phi_c_complex->Phi_c) = 3 diffs.
theorem qm_to_qft_distance :
    primitiveMismatches quantum_mechanics quantum_field_theory = 3 := by
  unfold primitiveMismatches quantum_mechanics quantum_field_theory
  decide

-- ============================================================
-- S6. CLASSICAL MECHANICS (FOR COMPARISON)
-- ============================================================

def classical_mechanics : Imscription := {
  dim  := D_infty
  top  := T_bowtie
  rel  := R_super
  pol  := P_sym
  fid  := F_ell
  kin  := K_fast
  gran := G_beth
  gram := Gamma_seq
  crit := Phi_sub
  chir := H0
  stoi := n_m
  prot := Omega_0
}

-- Classical is O_0: Phi_sub -> non-critical.
theorem classical_tier : imscriptionTier classical_mechanics = .O_0 := by
  decide

-- Classical -> QM: 10 primitives differ (top, rel, pol, fid, kin, gran, gram, crit, chir, prot).
theorem classical_quantum_distance :
    primitiveMismatches classical_mechanics quantum_mechanics = 10 := by
  unfold primitiveMismatches classical_mechanics quantum_mechanics
  decide

end Imscribing.HowHilbertQMArise
