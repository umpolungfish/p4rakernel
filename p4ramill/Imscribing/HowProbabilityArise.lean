-- Imscribing/HowProbabilityArise.lean
-- HOW PROBABILITY ARISES FROM THE GRAMMAR

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

namespace Imscribing.HowProbabilityArise

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.longLine false

-- ============================================================
-- S1. INFORMATION LOSS -> PROBABILITY
-- ============================================================

def with_fidelity (s : Imscription) (f : Fidelity) : Imscription :=
  { s with fid := f }

def information_loss (s : Imscription) : Nat :=
  primitiveMismatches s (with_fidelity s F_hbar)

theorem ell_has_loss (s : Imscription) (h : s.fid = F_ell) :
    information_loss s = 1 := by
  unfold information_loss with_fidelity primitiveMismatches
  simp [h]

theorem hbar_no_loss (s : Imscription) (h : s.fid = F_hbar) :
    information_loss s = 0 := by
  unfold information_loss with_fidelity primitiveMismatches
  simp [h]

-- ============================================================
-- S2. PROBABILITY AS NORMALIZED DISTANCE
-- ============================================================

def bottom_type : Imscription := {
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

def top_type : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_lr
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_MBL
  gran := G_aleph
  gram := Gamma_broad
  crit := Phi_super
  chir := H_inf
  stoi := n_m
  prot := Omega_NA
}

theorem max_distance_is_12 :
    primitiveMismatches bottom_type top_type = 12 := by
  unfold primitiveMismatches bottom_type top_type
  decide

def prob (s : Imscription) : Rat :=
  (primitiveMismatches bottom_type s) / 12

theorem prob_bottom_zero : prob bottom_type = 0 := by
  unfold prob
  have h := primitiveMismatches_self bottom_type
  rw [h]
  native_decide

theorem prob_top_one : prob top_type = 1 := by
  unfold prob
  rw [max_distance_is_12]
  native_decide

-- ============================================================
-- S3. BOLTZMANN WEIGHTS FROM KINETICS
-- ============================================================

def energy (s : Imscription) : Nat := primitiveMismatches bottom_type s

-- ============================================================
-- S4. FROBENIUS-EXACT COLLAPSE
-- ============================================================

def frobenius_prob (s t : Imscription) : Rat :=
  if s = t then 1 else 0

theorem frobenius_binary (s t : Imscription) :
    frobenius_prob s t = 0 ∨ frobenius_prob s t = 1 := by
  unfold frobenius_prob
  split
  · right; rfl
  · left; rfl

end Imscribing.HowProbabilityArise
