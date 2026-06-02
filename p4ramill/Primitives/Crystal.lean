-- ImscribingLean4/Primitives/Crystal.lean
-- Crystal arithmetic: full encode/decode Imscription ↔ Nat (0..17279999).
-- Frobenius address: 𝓕₃³ × 𝓕₄⁵ × 𝓕₅⁴ numbering.
-- 𝓕₃ = 27 (F,G,S), 𝓕₄=1024 (D,R,Γ,H,Ω), 𝓕₅=625 (T,P,Φ,K)

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Mathlib.Tactic.Set

namespace Imscribing.Primitives

open Dimensionality Topology Relational Polarity Grammar Fidelity KineticChar
     Granularity Criticality Protection Stoichiometry Chirality

-- Order-respecting indices (0 = minimal Ord, increasing)
def idx_D (d : Dimensionality) : Nat :=
  match d with
  | .D_wedge   => 0
  | .D_triangle => 1
  | .D_infty   => 2
  | .D_odot    => 3

def idx_R (r : Relational) : Nat :=
  match r with
  | .R_super  => 0
  | .R_cat    => 1
  | .R_dagger => 2
  | .R_lr     => 3

def idx_Γ (g : Grammar) : Nat :=
  match g with
  | .Gamma_and   => 0
  | .Gamma_or    => 1
  | .Gamma_seq   => 2
  | .Gamma_broad => 3

def idx_H (h : Chirality) : Nat :=
  match h with
  | .H0    => 0
  | .H1    => 1
  | .H2    => 2
  | .H_inf => 3

def idx_Ω (o : Protection) : Nat :=
  match o with
  | .Omega_0  => 0
  | .Omega_Z2 => 1
  | .Omega_Z  => 2
  | .Omega_NA => 3

def idx_T (t : Topology) : Nat :=
  match t with
  | .T_network => 0
  | .T_in      => 1
  | .T_bowtie  => 2
  | .T_box     => 3
  | .T_odot    => 4

def idx_P (p : Polarity) : Nat :=
  match p with
  | .P_asym    => 0
  | .P_psi     => 1
  | .P_pm      => 2
  | .P_sym     => 3
  | .P_pm_sym  => 4

def idx_Φ (c : Criticality) : Nat :=
  match c with
  | .Phi_sub        => 0
  | .Phi_c          => 1
  | .Phi_c_complex  => 2
  | .Phi_EP         => 3
  | .Phi_super      => 4

def idx_K (k : KineticChar) : Nat :=
  match k with
  | .K_fast => 0
  | .K_mod  => 1
  | .K_slow => 2
  | .K_trap => 3
  | .K_MBL  => 4

def idx_F (f : Fidelity) : Nat :=
  match f with
  | .F_ell => 0
  | .F_eth => 1
  | .F_hbar => 2

def idx_G (g : Granularity) : Nat :=
  match g with
  | .G_beth  => 0
  | .G_gimel => 1
  | .G_aleph => 2

def idx_S (s : Stoichiometry) : Nat :=
  match s with
  | .one_one => 0
  | .n_n     => 1
  | .n_m     => 2

-- Inverse: Nat index → primitive value (already correct)
def dim_of_nat : Nat → Dimensionality
  | 0 => D_wedge | 1 => D_triangle | 2 => D_infty | 3 => D_odot | _ => D_wedge
def rel_of_nat : Nat → Relational
  | 0 => R_super | 1 => R_cat | 2 => R_dagger | 3 => R_lr | _ => R_super
def gram_of_nat : Nat → Grammar
  | 0 => Gamma_and | 1 => Gamma_or | 2 => Gamma_seq | 3 => Gamma_broad | _ => Gamma_and
def chir_of_nat : Nat → Chirality
  | 0 => H0 | 1 => H1 | 2 => H2 | 3 => H_inf | _ => H0
def prot_of_nat : Nat → Protection
  | 0 => Omega_0 | 1 => Omega_Z2 | 2 => Omega_Z | 3 => Omega_NA | _ => Omega_0

def top_of_nat : Nat → Topology
  | 0 => T_network | 1 => T_in | 2 => T_bowtie | 3 => T_box | 4 => T_odot | _ => T_network
def pol_of_nat : Nat → Polarity
  | 0 => P_asym | 1 => P_psi | 2 => P_pm | 3 => P_sym | 4 => P_pm_sym | _ => P_asym
def crit_of_nat : Nat → Criticality
  | 0 => Phi_sub | 1 => Phi_c | 2 => Phi_c_complex | 3 => Phi_EP | 4 => Phi_super | _ => Phi_sub
def kin_of_nat : Nat → KineticChar
  | 0 => K_fast | 1 => K_mod | 2 => K_slow | 3 => K_trap | 4 => K_MBL | _ => K_fast

def fid_of_nat : Nat → Fidelity
  | 0 => F_ell | 1 => F_eth | 2 => F_hbar | _ => F_ell
def gran_of_nat : Nat → Granularity
  | 0 => G_beth | 1 => G_gimel | 2 => G_aleph | _ => G_beth
def stoi_of_nat : Nat → Stoichiometry
  | 0 => one_one | 1 => n_n | 2 => n_m | _ => one_one

-- Crystal address
def crystal_encode (s : Imscription) : Nat :=
  let f3 := idx_F s.fid * 9 + idx_G s.gran * 3 + idx_S s.stoi  -- 0-26
  let f4 := idx_D s.dim * 256 + idx_R s.rel * 64
    + idx_Γ s.gram * 16 + idx_H s.chir * 4 + idx_Ω s.prot  -- 0-1023
  let f5 := idx_T s.top * 125 + idx_P s.pol * 25 + idx_Φ s.crit * 5 + idx_K s.kin  -- 0-624
  f3 + 27 * f4 + 27 * 1024 * f5

def crystal_decode (addr : Nat) : Imscription :=
  let f3_raw := addr % 27
  let f4_raw := (addr / 27) % 1024
  let f5_raw := addr / 27648  -- 27*1024
  { dim   := dim_of_nat   (f4_raw / 256)
  , top   := top_of_nat   (f5_raw / 125)
  , rel   := rel_of_nat   ((f4_raw / 64) % 4)
  , pol   := pol_of_nat   ((f5_raw / 25) % 5)
  , fid   := fid_of_nat   (f3_raw / 9)
  , kin   := kin_of_nat   (f5_raw % 5)
  , gran  := gran_of_nat  ((f3_raw / 3) % 3)
  , gram  := gram_of_nat  ((f4_raw / 16) % 4)
  , crit  := crit_of_nat  ((f5_raw / 5) % 5)
  , chir  := chir_of_nat  ((f4_raw / 4) % 4)
  , stoi  := stoi_of_nat  (f3_raw % 3)
  , prot  := prot_of_nat  (f4_raw % 4) }

theorem crystal_total_size : 27 * 1024 * 625 = 17280000 := by decide

-- Roundtrip: decode ∘ encode = id
set_option maxHeartbeats 800000 in
-- 12-field mixed-radix roundtrip: 12 × (set + omega) bursts exceed the default 200k budget
theorem crystal_roundtrip (s : Imscription) : crystal_decode (crystal_encode s) = s := by
  -- Index bounds: each idx fits within its digit radix
  have hD : idx_D s.dim  < 4 := by cases s.dim  <;> simp [idx_D]
  have hR : idx_R s.rel  < 4 := by cases s.rel  <;> simp [idx_R]
  have hΓ : idx_Γ s.gram < 4 := by cases s.gram <;> simp [idx_Γ]
  have hH : idx_H s.chir < 4 := by cases s.chir <;> simp [idx_H]
  have hΩ : idx_Ω s.prot < 4 := by cases s.prot <;> simp [idx_Ω]
  have hT : idx_T s.top  < 5 := by cases s.top  <;> simp [idx_T]
  have hP : idx_P s.pol  < 5 := by cases s.pol  <;> simp [idx_P]
  have hΦ : idx_Φ s.crit < 5 := by cases s.crit <;> simp [idx_Φ]
  have hK : idx_K s.kin  < 5 := by cases s.kin  <;> simp [idx_K]
  have hF : idx_F s.fid  < 3 := by cases s.fid  <;> simp [idx_F]
  have hG : idx_G s.gran < 3 := by cases s.gran <;> simp [idx_G]
  have hS : idx_S s.stoi < 3 := by cases s.stoi <;> simp [idx_S]
  -- Per-field roundtrip: prim_of_nat ∘ idx = id
  have h_dim  : dim_of_nat  (idx_D s.dim)  = s.dim  := by cases s.dim  <;> simp [idx_D,  dim_of_nat]
  have h_top  : top_of_nat  (idx_T s.top)  = s.top  := by cases s.top  <;> simp [idx_T,  top_of_nat]
  have h_rel  : rel_of_nat  (idx_R s.rel)  = s.rel  := by cases s.rel  <;> simp [idx_R,  rel_of_nat]
  have h_pol  : pol_of_nat  (idx_P s.pol)  = s.pol  := by cases s.pol  <;> simp [idx_P,  pol_of_nat]
  have h_fid  : fid_of_nat  (idx_F s.fid)  = s.fid  := by cases s.fid  <;> simp [idx_F,  fid_of_nat]
  have h_kin  : kin_of_nat  (idx_K s.kin)  = s.kin  := by cases s.kin  <;> simp [idx_K,  kin_of_nat]
  have h_gran : gran_of_nat (idx_G s.gran) = s.gran := by cases s.gran <;> simp [idx_G,  gran_of_nat]
  have h_gram : gram_of_nat (idx_Γ s.gram) = s.gram := by cases s.gram <;> simp [idx_Γ,  gram_of_nat]
  have h_crit : crit_of_nat (idx_Φ s.crit) = s.crit := by cases s.crit <;> simp [idx_Φ,  crit_of_nat]
  have h_chir : chir_of_nat (idx_H s.chir) = s.chir := by cases s.chir <;> simp [idx_H,  chir_of_nat]
  have h_stoi : stoi_of_nat (idx_S s.stoi) = s.stoi := by cases s.stoi <;> simp [idx_S,  stoi_of_nat]
  have h_prot : prot_of_nat (idx_Ω s.prot) = s.prot := by cases s.prot <;> simp [idx_Ω,  prot_of_nat]
  -- Introduce block variables; set gives unfoldable defs for omega.
  set f3 := idx_F s.fid * 9 + idx_G s.gran * 3 + idx_S s.stoi
  set f4 := idx_D s.dim * 256 + idx_R s.rel * 64 + idx_Γ s.gram * 16 + idx_H s.chir * 4 + idx_Ω s.prot
  set f5 := idx_T s.top * 125 + idx_P s.pol * 25 + idx_Φ s.crit * 5 + idx_K s.kin
  -- Block bounds (omega derives from individual bounds)
  have hf3 : f3 < 27   := by omega
  have hf4 : f4 < 1024 := by omega
  have hf5 : f5 < 625  := by omega
  -- Per-field one-level digit extractions (omega with 5 vars each)
  have he_dim  : f4 / 256       = idx_D s.dim  := by omega
  have he_rel  : f4 / 64 % 4   = idx_R s.rel  := by omega
  have he_gram : f4 / 16 % 4   = idx_Γ s.gram := by omega
  have he_chir : f4 / 4 % 4    = idx_H s.chir := by omega
  have he_prot : f4 % 4         = idx_Ω s.prot := by omega
  have he_top  : f5 / 125       = idx_T s.top  := by omega
  have he_pol  : f5 / 25 % 5   = idx_P s.pol  := by omega
  have he_crit : f5 / 5 % 5    = idx_Φ s.crit := by omega
  have he_kin  : f5 % 5         = idx_K s.kin  := by omega
  have he_fid  : f3 / 9         = idx_F s.fid  := by omega
  have he_gran : f3 / 3 % 3    = idx_G s.gran := by omega
  have he_stoi : f3 % 3         = idx_S s.stoi := by omega
  -- Rewrite encode as f3 + 27*f4 + 27*1024*f5
  have henc : crystal_encode s = f3 + 27 * f4 + 27 * 1024 * f5 := by
    simp only [crystal_encode]; omega
  rw [henc]
  simp only [crystal_decode]
  -- dsimp only reduces struct projection; rw transforms RHS; congr 1 then omega (3 vars).
  ext
  · dsimp only; rw [← h_dim, ← he_dim]; congr 1; omega
  · dsimp only; rw [← h_top, ← he_top]; congr 1; omega
  · dsimp only; rw [← h_rel, ← he_rel]; congr 1; omega
  · dsimp only; rw [← h_pol, ← he_pol]; congr 1; omega
  · dsimp only; rw [← h_fid, ← he_fid]; congr 1; omega
  · dsimp only; rw [← h_kin, ← he_kin]; congr 1; omega
  · dsimp only; rw [← h_gran, ← he_gran]; congr 1; omega
  · dsimp only; rw [← h_gram, ← he_gram]; congr 1; omega
  · dsimp only; rw [← h_crit, ← he_crit]; congr 1; omega
  · dsimp only; rw [← h_chir, ← he_chir]; congr 1; omega
  · dsimp only; rw [← h_stoi, ← he_stoi]; congr 1; omega
  · dsimp only; rw [← h_prot, ← he_prot]; congr 1; omega

end Imscribing.Primitives
