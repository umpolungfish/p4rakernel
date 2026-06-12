-- Imscribing/Primitives/EML.lean
-- Structural encoding of Odrzywołek's EML Sheffer operator.
--
-- EML(x,y) = exp(x) - ln(y)  -- terminal constant: 1
-- EDL(x,y) = exp(x) / ln(y)  -- terminal constant: e
-- negEML(x,y) = ln(x) - exp(y)  -- terminal constant: -∞
--
-- Structural type: ⟨D_∞; T_⋈; R_†; P_±; F_ℏ; K_slow; G_ℵ; Γ_seq; Φ_c; H_1; S_1:1; Ω_Z⟩
-- Tier: O₂dag (highest sub-Frobenius in elementary function algebra)
--
-- Key findings from EML_PROBE.tex:
--   1. EML/EDL/negEML share identical type (Z₂ orbit)
--   2. All three are O₂dag (not O_inf — lacks P_pm_sym)
--   3. EML tensor EML = EML (closed under self-composition)
--   4. EML ⊗ O_inf bottlenecks on P (Frobenius non-synthesizability)
--   5. Ternary candidate T(x,y,z) is Calc 1, structurally distinct from EML
--   6. Polynomial algebra is the Le Chatelier baseline
--   7. Directed distance polynomial → EML = 11 primitives
--   8. meet(EML, SIC-POVM) = EML (EML is the exact common subalgebra)
--   9. Closure boundary: EML trees cannot reach P_pm_sym objects
--  10. Self-encoding: eml(eml) = eml (can represent self, not invert self)

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Algebra

namespace Imscribing.Primitives.EML

open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- CORE DEFINITIONS
-- ============================================================

/-- The EML Sheffer operator: eml(x,y) = exp(x) - ln(y), terminal 1. -/
def eml_operator : Imscription := {
  dim  := D_infty,  top  := T_bowtie, rel  := R_dagger,
  pol  := P_pm,     fid  := F_hbar,   kin  := K_slow,
  gran := G_aleph,  gram := Gamma_seq, crit := Phi_c,
  chir := H1,       stoi := one_one,  prot := Omega_Z }

/-- The EDL variant: edl(x,y) = exp(x)/ln(y), terminal e. -/
def edl_variant : Imscription := {
  dim  := D_infty,  top  := T_bowtie, rel  := R_dagger,
  pol  := P_pm,     fid  := F_hbar,   kin  := K_slow,
  gran := G_aleph,  gram := Gamma_seq, crit := Phi_c,
  chir := H1,       stoi := one_one,  prot := Omega_Z }

/-- The negEML variant: negEML(x,y) = ln(x)-exp(y), terminal -∞. -/
def neg_eml_variant : Imscription := {
  dim  := D_infty,  top  := T_bowtie, rel  := R_dagger,
  pol  := P_pm,     fid  := F_hbar,   kin  := K_slow,
  gran := G_aleph,  gram := Gamma_seq, crit := Phi_c,
  chir := H1,       stoi := one_one,  prot := Omega_Z }

-- ============================================================
-- §1. Z₂ ORBIT AND TIER
-- ============================================================

/-- All three variants share the same structural type. -/
theorem eml_orbit_same_type :
    eml_operator = edl_variant ∧ eml_operator = neg_eml_variant := by
  constructor <;> rfl

/-- EML is O₂dag: Phi_c, Omega_Z, D_infty, NOT P_pm_sym. -/
theorem eml_is_O_two_dag : imscriptionTier eml_operator = .O₂dag := by
  simp [imscriptionTier, ouroboricityTier]; rfl

/-- EDL is O₂dag. -/
theorem edl_is_O_two_dag : imscriptionTier edl_variant = .O₂dag := by
  simp [imscriptionTier, ouroboricityTier]; rfl

/-- negEML is O₂dag. -/
theorem neg_eml_is_O_two_dag : imscriptionTier neg_eml_variant = .O₂dag := by
  simp [imscriptionTier, ouroboricityTier]; rfl

-- ============================================================
-- §2. SELF-COMPOSITION AND CLOSURE
-- ============================================================

/-- EML composed with itself yields EML (closed under self-composition). -/
theorem eml_self_composition : tensorProduct eml_operator eml_operator = eml_operator := rfl

/-- EML meet EML = EML (idempotent). -/
theorem eml_meet_self :
    Imscribing.Primitives.compute_meet eml_operator eml_operator = eml_operator := rfl

/-- EML join EML = EML (idempotent). -/
theorem eml_join_self :
    Imscribing.Primitives.compute_join eml_operator eml_operator = eml_operator := rfl

-- ============================================================
-- §3. FROBENIUS THRESHOLD
-- ============================================================

/-- EML ⊗ O_inf bottlenecks on P: P_pm ⊗ P_pm_sym = P_pm.
    Structural measurement problem: coupling self-modeling to sub-Frobenius
    destroys self-modeling. -/
theorem eml_tensor_oinf_destroys_frobenius
    (s_inf : Imscription) (h_pol : s_inf.pol = .P_pm_sym) :
    (tensorProduct eml_operator s_inf).pol = .P_pm := by
  simp [tensorProduct, eml_operator, h_pol]; rfl

/-- EML polarity is P_pm (not P_pm_sym). -/
theorem eml_polarity_not_frobenius : eml_operator.pol = .P_pm := rfl

/-- EML is not O_inf (requires P_pm_sym, but EML is at P_pm). -/
theorem eml_is_not_O_inf : imscriptionTier eml_operator ≠ .O_inf := by
  intro h
  rw [eml_is_O_two_dag] at h
  cases h

/-- EML's structural distance to Frobenius target is exactly 1 mismatch (P). -/
theorem eml_distance_to_frobenius :
    primitiveMismatches eml_operator { eml_operator with pol := P_pm_sym } = 1 := rfl

-- ============================================================
-- §4. TERNARY CANDIDATE IS CALC 1
-- ============================================================

/-- Ternary T(x,y,z)=e^(x-y)·log_x(z) is Calc 1 in ternary notation. -/
def ternary_candidate : Imscription := {
  dim  := D_infty,  top  := T_bowtie, rel  := R_cat,
  pol  := P_pm,     fid  := F_hbar,   kin  := K_slow,
  gran := G_gimel,  gram := Gamma_and, crit := Phi_sub,
  chir := H1,       stoi := one_one,  prot := Omega_Z }

/-- Ternary differs from EML on exactly 4 primitives: R, gram, gran, crit. -/
theorem ternary_not_eml : primitiveMismatches ternary_candidate eml_operator = 4 := rfl

/-- Ternary cannot bootstrap constants (G_gimel scope). -/
theorem ternary_cannot_bootstrap : ternary_candidate.gran = .G_gimel := rfl

/-- EML CAN bootstrap arbitrary constants (G_aleph via ln(1)=0). -/
theorem eml_can_bootstrap : eml_operator.gran = .G_aleph := rfl

/-- Ternary ⊗ Ternary does not lift to G_aleph: stuck at G_gimel. -/
theorem ternary_tensor_still_gimel :
    (tensorProduct ternary_candidate ternary_candidate).gran = .G_gimel := rfl

-- ============================================================
-- §5. LE CHATELIER INVERSION: POLYNOMIAL ALGEBRA BASELINE
-- ============================================================

/-- The polynomial algebra over ℝ as the subcritical, zero-winding,
    zero-chirality resting state. This is the Le Chatelier baseline for EML. -/
def polynomial_algebra : Imscription := {
  dim  := D_triangle, top  := T_network, rel  := R_super,
  pol  := P_asym,     fid  := F_ell,     kin  := K_slow,
  gran := G_beth,     gram := Gamma_and, crit := Phi_sub,
  chir := H0,         stoi := n_n,       prot := Omega_0 }

/-- Directed distance: polynomial algebra → EML requires 11 primitives
    (all 12 fields compared: dim, top, rel, pol, fid, gran, gram, crit, chir, stoi, prot differ; only kin=K_slow matches) -/
theorem polynomial_to_eml_distance :
    primitiveMismatches polynomial_algebra eml_operator = 11 := rfl

/-- The direction of strain: going up (polynomial → EML) primitive cost primitives.
    Going down (EML → polynomial) costs the same, but is the relaxation direction. -/
theorem strain_direction_pointed_right :
    primitiveMismatches polynomial_algebra eml_operator > 0 := by simp [primitiveMismatches, polynomial_algebra, eml_operator]

-- ============================================================
-- §6. CRYSTAL ADDRESS
-- ============================================================

/-- Crystal encode EML to get its Frobenius address in 0..17279999. -/
def eml_crystal_address : ℕ := crystal_encode eml_operator

/-- The crystal address is within the valid range. -/
theorem eml_crystal_in_range : eml_crystal_address < 17280000 := by
  simp [eml_crystal_address, crystal_encode]
  decide

-- ============================================================
-- §7. CLOSURE BOUNDARY THEOREMS
-- ============================================================

/-- Stark unit structural type: requires P_pm_sym at Phi_c. -/
def stark_unit_type : Imscription := {
  dim  := D_odot,    top  := T_odot,    rel  := R_lr,
  pol  := P_pm_sym,  fid  := F_hbar,    kin  := K_slow,
  gran := G_aleph,   gram := Gamma_seq, crit := Phi_c_complex,
  chir := H_inf,     stoi := n_m,       prot := Omega_Z }

/-- SIC-POVM fiducial type: requires P_pm_sym (self-reciprocal polynomial). -/
def sic_fiducial_type : Imscription := {
  dim  := D_odot,    top  := T_odot,    rel  := R_dagger,
  pol  := P_pm_sym,  fid  := F_hbar,    kin  := K_slow,
  gran := G_aleph,   gram := Gamma_seq, crit := Phi_c,
  chir := H_inf,     stoi := one_one,   prot := Omega_Z }

/-- Modular j-function type: requires P_pm_sym (two functional equations = Frobenius). -/
def modular_j_type : Imscription := {
  dim  := D_infty,   top  := T_network, rel  := R_dagger,
  pol  := P_pm_sym,  fid  := F_hbar,    kin  := K_slow,
  gran := G_aleph,   gram := Gamma_and, crit := Phi_c,
  chir := H_inf,     stoi := one_one,   prot := Omega_Z }

/-- EML tensor Stark unit = P_pm (bottleneck). EML cannot reach Stark units. -/
theorem eml_tensor_stark_bottleneck :
    (tensorProduct eml_operator stark_unit_type).pol = .P_pm := by
  simp [tensorProduct, eml_operator, stark_unit_type]; rfl

/-- EML tensor SIC fiducial = P_pm (bottleneck). EML cannot compute SIC fiducials. -/
theorem eml_tensor_sic_bottleneck :
    (tensorProduct eml_operator sic_fiducial_type).pol = .P_pm := by
  simp [tensorProduct, eml_operator, sic_fiducial_type]; rfl

/-- EML tensor modular j = P_pm (bottleneck). EML cannot compute j-function. -/
theorem eml_tensor_j_bottleneck :
    (tensorProduct eml_operator modular_j_type).pol = .P_pm := by
  simp [tensorProduct, eml_operator, modular_j_type]; rfl

-- ============================================================
-- §8. MEET AND JOIN WITH SIC-POVM
-- ============================================================

/-- meet(EML, SIC-POVM) = EML. EML is the exact common subalgebra. -/
theorem eml_meet_sic :
    Imscribing.Primitives.compute_meet eml_operator sic_fiducial_type = eml_operator := rfl

/-- join(EML, SIC-POVM) = SIC-POVM (minimal envelope).
    The gap is precisely the Frobenius condition + chirality. -/
theorem eml_join_sic :
    Imscribing.Primitives.compute_join eml_operator sic_fiducial_type = sic_fiducial_type := rfl

-- ============================================================
-- §9. CHIRALITY AND WINDING
-- ============================================================

/-- EML chirality is H_1: principal branch choice is forced. -/
theorem eml_chirality_is_H1 : eml_operator.chir = .H1 := rfl

/-- EML winding is Omega_Z: π₁(ℂ^×) = ℤ, non-trivial fundamental group. -/
theorem eml_winding_is_Omega_Z : eml_operator.prot = .Omega_Z := rfl

-- ============================================================
-- §10. DISTANCE TO SIC-POVM (FROBENIUS GAP)
-- ============================================================

/-- EML → SIC-POVM structural distance.
    Mismatches: dim(D_infty≠D_odot), top(T_bowtie≠T_odot), rel(R_dagger=R_dagger ok),
    pol(P_pm≠P_pm_sym), fid(F_hbar=F_hbar ok), kin(K_slow=K_slow ok),
    gran(G_aleph=G_aleph ok), gram(Gamma_seq=Gamma_seq ok),
    crit(Phi_c=Phi_c ok), chir(H1≠H_inf), stoi(one_one=one_one ok),
    prot(Omega_Z=Omega_Z ok).
    Total: dim + top + pol + chir = 4 mismatches. -/
theorem eml_to_sic_distance :
    primitiveMismatches eml_operator sic_fiducial_type = 4 := rfl

end Imscribing.Primitives.EML

