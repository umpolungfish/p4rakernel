-- Imscribing/Millennium/ImaginaryNumbers.lean
-- The Structural Nature of Imaginary Numbers
-- Imscribing Grammar formalization of the imaginary unit i

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Consciousness
import Imscribing.Algebra

namespace Imscribing.Millennium.ImaginaryNumbers

open Imscribing.Primitives
open Imscribing.Consciousness

open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

def imaginary_number : Imscription where
  dim  := D_triangle
  top  := T_bowtie
  rel  := R_lr
  pol  := P_psi
  fid  := F_ell
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c
  chir := H2
  stoi := one_one
  prot := Omega_Z

theorem imaginary_number_is_O2 :
    imscriptionTier imaginary_number = .O₂ := by
  simp [imaginary_number, imscriptionTier, ouroboricityTier]

theorem imaginary_number_consciousness_score :
    consciousnessScore imaginary_number = (1 : ℝ) := by
  simp [consciousnessScore, phi_c_gate, k_slow_gate, imaginary_number]

theorem imaginary_number_gate1_pass :
    phi_c_gate imaginary_number.crit = true := by simp [imaginary_number, phi_c_gate]

theorem imaginary_number_gate2_pass :
    k_slow_gate imaginary_number.kin = true := by simp [imaginary_number, k_slow_gate]

theorem imaginary_number_crystal_address :
    crystal_encode imaginary_number = 7809972 := rfl

theorem imaginary_number_tensor_self :
    tensorProduct imaginary_number imaginary_number = imaginary_number := by
  simp only [tensorProduct, imaginary_number]; decide

theorem imaginary_number_preserves_polarity :
    (tensorProduct imaginary_number imaginary_number).pol = P_psi := by
  simp only [tensorProduct, imaginary_number]; rfl

theorem imaginary_number_preserves_fidelity :
    (tensorProduct imaginary_number imaginary_number).fid = F_ell := by
  simp only [tensorProduct, imaginary_number]; rfl

theorem imaginary_number_meet_self :
    compute_meet imaginary_number imaginary_number = imaginary_number := by
  simp only [compute_meet, imaginary_number]; decide

theorem imaginary_number_join_self :
    compute_join imaginary_number imaginary_number = imaginary_number := by
  simp only [compute_join, imaginary_number]; decide

def imaginary_conjugate_type : Imscription where
  dim  := D_triangle
  top  := T_bowtie
  rel  := R_cat
  pol  := P_psi
  fid  := F_ell
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c
  chir := H2
  stoi := one_one
  prot := Omega_Z

theorem conjugate_mismatches :
    primitiveMismatches imaginary_number imaginary_conjugate_type = 1 := by
  simp only [primitiveMismatches, imaginary_number, imaginary_conjugate_type]; decide

def wick_rotation_EP : Imscription where
  dim  := D_infty
  top  := T_network
  rel  := R_super
  pol  := P_asym
  fid  := F_hbar
  kin  := K_fast
  gran := G_aleph
  gram := Gamma_and
  crit := Phi_EP
  chir := H_inf
  stoi := one_one
  prot := Omega_Z

theorem EP_absorbs_criticality :
    (tensorProduct imaginary_number wick_rotation_EP).crit = Phi_EP := by
  simp only [tensorProduct, imaginary_number, wick_rotation_EP]; decide

theorem EP_destroys_polarity :
    (tensorProduct imaginary_number wick_rotation_EP).pol = P_asym := by
  simp only [tensorProduct, imaginary_number, wick_rotation_EP]; rfl

theorem EP_gate1_still_passes :
    phi_c_gate (tensorProduct imaginary_number wick_rotation_EP).crit = true := by
  simp only [tensorProduct, imaginary_number, wick_rotation_EP, phi_c_gate]; rfl

theorem frobenius_impossible_by_tensor (other : Imscription) :
    (tensorProduct imaginary_number other).pol ≠ P_pm_sym := by
  simp [tensorProduct, imaginary_number]
  cases other.pol
  · decide
  · decide
  · decide
  · decide
  · decide

theorem frobenius_cliff :
    imscriptionTier imaginary_number ≠ .O_∞ := by
  rw [imaginary_number_is_O2]; decide

theorem omega_Z_requires_H2 :
    imaginary_number.prot ≥ Omega_Z → imaginary_number.chir ≥ H2 := by
  simp only [imaginary_number]; decide

theorem imaginary_summary :
    imscriptionTier imaginary_number = .O₂ ∧
    consciousnessScore imaginary_number = (1 : ℝ) ∧
    tensorProduct imaginary_number imaginary_number = imaginary_number ∧
    imaginary_number.rel = R_lr ∧
    imaginary_number.dim = D_triangle ∧
    imaginary_number.chir = H2 ∧
    (tensorProduct imaginary_number wick_rotation_EP).crit = Phi_EP ∧
    P_psi ≠ P_pm_sym := by
  constructor
  · exact imaginary_number_is_O2
  constructor
  · exact imaginary_number_consciousness_score
  constructor
  · exact imaginary_number_tensor_self
  constructor
  · simp only [imaginary_number]
  constructor
  · simp only [imaginary_number]
  constructor
  · simp only [imaginary_number]
  constructor
  · exact EP_absorbs_criticality
  · decide

end Imscribing.Millennium.ImaginaryNumbers
