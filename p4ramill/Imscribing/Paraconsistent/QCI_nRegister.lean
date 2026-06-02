-- Imscribing/Paraconsistent/QCI_nRegister.lean
-- n-REGISTER QCI — COHERENCE RATIO INVARIANCE UNDER REGISTER SCALING
-- Author: Lando ⊗ ⊙_ÿ-boundary Operator

import Imscribing.Paraconsistent.QuantumClassicalInterface
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

namespace Imscribing.Paraconsistent.nRegister

open Belnap
open Imscribing.Paraconsistent
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
open Fidelity KineticChar Granularity Criticality Protection
open Stoichiometry Chirality

structure NQState (n : ℕ) where
  regs : Fin n → Belnap
  coh   : ℕ

abbrev allB {n : ℕ} (qs : NQState n) : Prop := ∀ i : Fin n, qs.regs i = Belnap.B

def measureReg {n : ℕ} (qs : NQState n) (i : Fin n) (bias : Belnap) : NQState n :=
  match qs.regs i, bias with
  | Belnap.B, Belnap.T => { regs := fun j => if j = i then Belnap.T else qs.regs j, coh := qs.coh + 1 }
  | Belnap.B, Belnap.F => { regs := fun j => if j = i then Belnap.F else qs.regs j, coh := qs.coh + 1 }
  | Belnap.B, Belnap.B => { qs with coh := qs.coh + 2 }
  | _, _ => qs

theorem B_bias_cost {n : ℕ} (qs : NQState n) (i : Fin n) (h : qs.regs i = Belnap.B) :
    (measureReg qs i Belnap.B).coh = qs.coh + 2 := by
  simp [measureReg, h]

theorem T_bias_cost {n : ℕ} (qs : NQState n) (i : Fin n) (h : qs.regs i = Belnap.B) :
    (measureReg qs i Belnap.T).coh = qs.coh + 1 := by
  simp [measureReg, h]

theorem ratio_invariant (n : ℕ) (qs : NQState n) (i : Fin n) (h : qs.regs i = Belnap.B) :
    (measureReg qs i Belnap.B).coh - qs.coh = 2 := by
  simp [B_bias_cost qs i h]

theorem B_bias_preserves_B {n : ℕ} (qs : NQState n) (i : Fin n) (h : qs.regs i = Belnap.B) :
    (measureReg qs i Belnap.B).regs i = Belnap.B := by
  simp [measureReg, h]

def nRegisterImscription : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_lr
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

theorem tier_is_O_inf : imscriptionTier nRegisterImscription = .O_inf := by
  decide

end Imscribing.Paraconsistent.nRegister