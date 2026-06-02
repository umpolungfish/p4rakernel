-- Imscribing/Millennium/CompositionRules.lean

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.ZFCt
import Imscribing.Algebra

namespace Millennium.CompositionRules

set_option linter.style.setOption false

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
  Fidelity KineticChar Granularity Criticality Protection
  Stoichiometry Chirality

def IsFrobenius (s : Imscription) : Prop := s.pol = P_pm_sym

theorem tensorPol_eq (s t : Imscription) :
    (tensorProduct s t).pol =
      if compare s.pol t.pol = .lt then s.pol else t.pol := rfl

set_option maxHeartbeats 60000 in
-- cases a <;> cases b generates 25 Polarity-pair goals; simp needs the extra budget
set_option linter.unnecessarySeqFocus false in
/-- If tensor product polarity is P_pm_sym then both must be P_pm_sym -/
lemma polTensor_implies_both {a b : Polarity} :
    (if compare a b = .lt then a else b) = P_pm_sym → a = P_pm_sym ∧ b = P_pm_sym := by
  intro h
  cases a <;> cases b <;> simp [compare] at h
  <;> (try contradiction)
  <;> simp_all

theorem RFROB_BARR_simple {a b : Imscription} :
    (tensorProduct a b).pol = P_pm_sym → a.pol = P_pm_sym ∧ b.pol = P_pm_sym := by
  intro h
  rw [tensorPol_eq a b] at h
  exact polTensor_implies_both h

theorem RFROB_CONT_frobenius_closure {a b : Imscription} :
    a.pol = P_pm_sym → b.pol = P_pm_sym →
    (tensorProduct a b).pol = P_pm_sym := by
  intro ha hb
  rw [tensorPol_eq a b, ha, hb]
  have : compare P_pm_sym P_pm_sym = .eq := by decide
  simp [this]

def IsFixpoint (s : Imscription) : Prop := imscriptionTier s = .O_inf

theorem RFIXPT_T_fixpoint_requires_frobenius {s : Imscription} :
    IsFixpoint s → s.pol = P_pm_sym := by
  intro hfix
  rcases (o_inf_iff_P_pm_sym_at_phi_c s).mp hfix with ⟨_, hpol⟩
  exact hpol

theorem zfc_zfct_six_promotions :
    primitiveMismatches ZFCt.zfc ZFCt.zfc_t = 6 := by
  simp [ZFCt.zfc, ZFCt.zfc_t, primitiveMismatches]

lemma tensor_zfc_zfct_polarity :
    (tensorProduct ZFCt.zfc ZFCt.zfc_t).pol = P_asym := by
  rw [tensorPol_eq, ZFCt.zfc, ZFCt.zfc_t]; decide

lemma meet_zfc_zfct_polarity :
    (compute_meet ZFCt.zfc ZFCt.zfc_t).pol = P_asym := by
  unfold compute_meet; rw [ZFCt.zfc, ZFCt.zfc_t]; decide

theorem IMPOSS_tensor_zfc_zfct_not_O_inf :
    imscriptionTier (tensorProduct ZFCt.zfc ZFCt.zfc_t) ≠ .O_inf := by
  intro h
  have hpol := RFIXPT_T_fixpoint_requires_frobenius h
  rw [tensor_zfc_zfct_polarity] at hpol
  contradiction

theorem IMPOSS_meet_zfc_zfct_not_O_inf :
    imscriptionTier (compute_meet ZFCt.zfc ZFCt.zfc_t) ≠ .O_inf := by
  intro h
  have hpol := RFIXPT_T_fixpoint_requires_frobenius h
  rw [meet_zfc_zfct_polarity] at hpol
  contradiction

theorem FROB_GEN_no_tensor_from_below {a b : Imscription} :
    a.pol < P_pm_sym → b.pol < P_pm_sym →
    (tensorProduct a b).pol < P_pm_sym := by
  intro ha hb
  rw [tensorPol_eq a b]
  by_cases h : compare a.pol b.pol = .lt
  · simp only [h]; exact ha
  · simp only [h]; exact hb

end Millennium.CompositionRules
