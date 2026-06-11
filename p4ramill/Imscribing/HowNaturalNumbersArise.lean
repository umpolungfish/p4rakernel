-- Imscribing/HowNaturalNumbersArise.lean
-- HOW NATURAL NUMBERS ARISE FROM THE GRAMMAR

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal

namespace Imscribing.HowNaturalNumbersArise

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.longLine false

-- ============================================================
-- S1. THE ZERO TYPE
-- ============================================================

def zero_type : Imscription := {
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

theorem zero_address : crystal_encode zero_type = 0 := by decide
theorem zero_tier : imscriptionTier zero_type = .O₀ := by decide

-- ============================================================
-- S2. SUCCESSOR TYPE AND OPERATION
-- ============================================================

def succ_type : Imscription := {
  zero_type with
  fid  := F_hbar
  gran := G_aleph
}

def succ (n : Imscription) : Imscription := tensorProduct n succ_type

theorem succ_zero_distinct : succ zero_type ≠ zero_type := by
  unfold succ tensorProduct succ_type zero_type
  decide

theorem succ_zero_distance :
    primitiveMismatches zero_type (succ zero_type) = 1 := by
  unfold succ succ_type tensorProduct primitiveMismatches zero_type
  decide

-- ============================================================
-- S3. CRYSTAL ADDRESS SPACE = N
-- ============================================================

theorem crystal_total : 27 * 1024 * 625 = 17280000 := by decide

-- ============================================================
-- S4. THE COUNTING PRIMITIVE: GRANULARITY
-- ============================================================

def counting_step (t : Imscription) : Imscription :=
  { t with gran :=
    match t.gran with
    | G_beth  => G_gimel
    | G_gimel => G_aleph
    | G_aleph => G_aleph
  }

theorem three_steps_to_aleph :
    (counting_step (counting_step (counting_step zero_type))).gran = G_aleph := by
  decide

-- ============================================================
-- S5. PEANO AXIOMS
-- ============================================================

lemma succ_gran_eq_aleph (n : Imscription) : (tensorProduct n succ_type).gran = G_aleph := by
  unfold tensorProduct succ_type
  cases h : n.gran with
  | G_beth =>
    simp [h]
    decide
  | G_gimel =>
    simp [h]
    decide
  | G_aleph =>
    simp [h]

theorem zero_not_succ (n : Imscription) : succ n ≠ zero_type := by
  unfold succ
  intro h
  have hgran := congrArg (fun s : Imscription => s.gran) h
  have hsucc_gran := succ_gran_eq_aleph n
  have hzero_gran : zero_type.gran = G_beth := rfl
  have : G_aleph ≠ G_beth := by decide
  apply this
  calc
    G_aleph = (tensorProduct n succ_type).gran := by symm; exact hsucc_gran
    _ = zero_type.gran := hgran
    _ = G_beth := hzero_gran

theorem succ_zero_not_zero : succ zero_type ≠ zero_type := by
  exact zero_not_succ zero_type

-- ============================================================
-- S6. MONOID STRUCTURE
-- ============================================================

def neutral_type : Imscription := {
  dim  := D_wedge
  top  := T_network
  rel  := R_super
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_fast
  gran := G_beth
  gram := Gamma_and
  crit := Phi_sub
  chir := H0
  stoi := one_one
  prot := Omega_0
}

theorem tensor_left_id (n : Imscription) : tensorProduct neutral_type n = n := by
  unfold tensorProduct neutral_type
  ext
  · cases n.dim <;> rfl
  · cases n.top <;> rfl
  · cases n.rel <;> rfl
  · cases n.pol <;> rfl
  · cases n.fid <;> rfl
  · cases n.kin <;> rfl
  · cases n.gran <;> rfl
  · cases n.gram <;> rfl
  · cases n.crit <;> rfl
  · cases n.chir <;> rfl
  · cases n.stoi <;> rfl
  · cases n.prot <;> rfl

theorem tensor_right_id (n : Imscription) : tensorProduct n neutral_type = n := by
  unfold tensorProduct neutral_type
  ext
  · cases n.dim <;> rfl
  · cases n.top <;> rfl
  · cases n.rel <;> rfl
  · cases n.pol <;> rfl
  · cases n.fid <;> rfl
  · cases n.kin <;> rfl
  · cases n.gran <;> rfl
  · cases n.gram <;> rfl
  · cases n.crit <;> rfl
  · cases n.chir <;> rfl
  · cases n.stoi <;> rfl
  · cases n.prot <;> rfl

end Imscribing.HowNaturalNumbersArise
