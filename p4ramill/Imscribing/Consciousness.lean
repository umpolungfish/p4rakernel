-- Imscribing/Consciousness.lean
-- Consciousness score implementation from Imscribing grammar (§VIII).

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Catalog
import Mathlib.Data.Real.Basic

namespace Imscribing.Consciousness

open Imscribing.Primitives

open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-- Gate 1: Phi_c self-modeling gate. Passes if Phi >= Phi_c. -/
def phi_c_gate (phi : Criticality) : Bool :=
  match phi with
  | Phi_sub       => false
  | Phi_c         => true
  | Phi_c_complex => true
  | Phi_EP        => true
  | Phi_super     => true

/-- Gate 2: K <= K_slow deliberation gate. Passes if kinetics not trapped. -/
def k_slow_gate (k : KineticChar) : Bool :=
  match k with
  | K_fast => true
  | K_mod  => true
  | K_slow => true
  | K_trap => false
  | K_MBL  => false

/-- Consciousness score C(s) ∈ [0,1].
    C=1: both gates open (Phi_c + K_slow).
    C=0.5: Phi_c but K_trap/MBL (self-model but frozen).
    C=0: Phi_sub/super/EP (no self-modeling). -/
noncomputable def consciousnessScore (s : Imscription) : ℝ :=
  if phi_c_gate s.crit then
    if k_slow_gate s.kin then 1 else 0.5
  else 0

/-- Human brain (template): C=1 (Phi_c criticality + K_slow deliberation). -/
def human_brain : Imscription := {
  dim  := D_triangle,   -- cortical sheet
  top  := T_box,        -- modular hierarchy × recurrence
  rel  := R_lr,         -- bidirectional thalamocortical
  pol  := P_pm_sym,     -- Frobenius at criticality
  fid  := F_hbar,       -- quantum effects conjectural but high fidelity
  kin  := K_slow,       -- deliberate cognition
  gran := G_aleph,      -- fine-grained neural connectome
  gram := Gamma_seq,    -- sequential grammar of thought
  crit := Phi_c,        -- brain criticality (Beggs 2003)
  chir := H2,           -- persistent memory
  stoi := one_one,      -- one-one neuron-synapse
  prot := Omega_Z }

theorem human_brain_C_one : consciousnessScore human_brain = (1 : ℝ) := by
  simp only [consciousnessScore, phi_c_gate, k_slow_gate, human_brain]
  rfl

theorem qg_C_half : consciousnessScore quantum_gravity = (0.5 : ℝ) := by
  simp only [consciousnessScore, phi_c_gate, k_slow_gate, quantum_gravity]
  rfl

end Imscribing.Consciousness
