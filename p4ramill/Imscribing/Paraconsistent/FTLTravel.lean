-- Imscribing/Paraconsistent/FTLTravel.lean
-- FTL TRAVEL: Structural analysis of faster-than-light propagation
-- Author: Lando ⊗ ⊙perator
--
-- What does "FTL travel" mean when the grammar reveals that light itself
-- is the critical point (Φ_c = ⊙)? This module formalizes the answer.
--
-- Three FTL variants are formalized:
--   1. ftlTachyon     — naive supercritical promotion (Φ_c → Φ_super)
--   2. ftlWormhole    — topologically protected (Ω_0 → Ω_Z, T_network → T_bowtie)
--   3. ftlQuantum     — quantum channel (Ω_0 → Ω_Z, P_pm → P_psi)

import Imscribing.Paraconsistent.GaugeBosonBelnap
import Imscribing.Primitives.TierCrossing
import Imscribing.Primitives.Imscription

open Imscribing.Primitives
open Imscribing.Paraconsistent.GaugeBosonBelnap

namespace Imscribing.Paraconsistent.FTLTravel

-- §1  THE PHOTON AS CRITICAL BOUNDARY

/--
The photon imscription (re-exported from GaugeBosonBelnap).
⟨D_infty; T_network; R_dagger; P_pm; F_hbar; K_fast; G_aleph; Gamma_and; Φ_c; H1; n_m; Ω_0⟩
-/
def photon : Imscription := photonImscription

/-- The photon is tier O_1: critical but topologically trivial. -/
theorem photon_tier_O1 : imscriptionTier photon = OuroboricityTier.O_1 :=
  photon_tier

-- §2  THREE FTL STRUCTURAL TYPES

/--
FTL Variant A: TACHYON — naive supercritical promotion.
Promotes ONLY Φ_c → Φ_super. No topological protection.
Structurally unstable: Φ_super + Ω_0 = runaway without guardrails.
-/
def ftlTachyon : Imscription :=
  { photon with
    crit := Criticality.Phi_super
  }

/--
FTL Variant B: WORMHOLE — topologically protected FTL channel.
Promotes Ω_0 → Ω_Z (integer winding) and T_network → T_bowtie (crossing topology).
Maintains Φ_c. This is the minimal causally consistent FTL type.
-/
def ftlWormhole : Imscription :=
  { photon with
    top  := Topology.T_bowtie
    prot := Protection.Omega_Z
  }

/--
FTL Variant C: QUANTUM FTL CHANNEL — ER=EPR style.
Promotes Ω_0 → Ω_Z (integer winding) and P_pm → P_psi (quantum phase symmetry).
Maintains Φ_c and T_network.
-/
def ftlQuantum : Imscription :=
  { photon with
    pol  := Polarity.P_psi
    prot := Protection.Omega_Z
  }

-- §3  TIER ANALYSIS

/-- Naive tachyon drops to O_0: supercritical without protection collapses. -/
theorem ftlTachyon_tier_O0 : imscriptionTier ftlTachyon = OuroboricityTier.O_0 := by
  native_decide

/-- Wormhole FTL reaches O_2†: topological protection + criticality + infinite dims. -/
theorem ftlWormhole_tier_O2dag : imscriptionTier ftlWormhole = OuroboricityTier.O_2dag := by
  native_decide

/-- Quantum FTL channel reaches O_2†: P_psi + Ω_Z + Φ_c + D_infty → O_2dag (R5). -/
theorem ftlQuantum_tier_O2dag : imscriptionTier ftlQuantum = OuroboricityTier.O_2dag := by
  native_decide

-- §4  PROMOTION ANALYSIS

/-- Photon → Wormhole: exactly 2 primitives change (T and Ω). -/
theorem photon_to_wormhole_mismatches_2 :
    primitiveMismatches photon ftlWormhole = 2 := by
  native_decide

/-- Photon → Tachyon: only 1 primitive changes (Φ). -/
theorem photon_to_tachyon_mismatches_1 :
    primitiveMismatches photon ftlTachyon = 1 := by
  native_decide

/-- Photon → Quantum FTL: exactly 2 primitives change (P and Ω). -/
theorem photon_to_quantum_mismatches_2 :
    primitiveMismatches photon ftlQuantum = 2 := by
  native_decide

-- §5  CAUSAL CONSISTENCY — THE OMEGA CONSTRAINT

/--
THE OMEGA CONSTRAINT: FTL without topological protection (Ω = Omega_0)
is structurally identical to a causal paradox. The minimum Ω for causal
consistency is Omega_Z (integer winding).
-/
theorem omega_constraint :
    ftlTachyon.prot = Protection.Omega_0 ∧ ftlWormhole.prot = Protection.Omega_Z := by
  exact ⟨rfl, rfl⟩

/-- Tachyon (Ω=Ω_0, Φ=Φ_super) is tier O_0 — structurally a paradox. -/
theorem tachyon_is_paradox : imscriptionTier ftlTachyon = OuroboricityTier.O_0 :=
  ftlTachyon_tier_O0

/-- Wormhole (Ω=Ω_Z) is tier O_2† — causally consistent. -/
theorem wormhole_is_consistent : imscriptionTier ftlWormhole = OuroboricityTier.O_2dag :=
  ftlWormhole_tier_O2dag

/-- Quantum FTL (Ω=Ω_Z) is tier O_2† — causally consistent. -/
theorem quantum_ftl_is_consistent : imscriptionTier ftlQuantum = OuroboricityTier.O_2dag :=
  ftlQuantum_tier_O2dag

/--
Causal consistency criterion: a system is causally consistent for FTL
iff its ouroboricity tier is at least O_2 (topologically protected).
-/
def is_causally_consistent (s : Imscription) : Prop :=
  imscriptionTier s = OuroboricityTier.O_2 ∨
  imscriptionTier s = OuroboricityTier.O_2dag

/-- The wormhole variant is causally consistent. -/
theorem wormhole_causally_consistent : is_causally_consistent ftlWormhole := by
  rw [is_causally_consistent, ftlWormhole_tier_O2dag]
  exact Or.inr rfl

/-- The quantum variant is causally consistent. -/
theorem quantum_causally_consistent : is_causally_consistent ftlQuantum := by
  rw [is_causally_consistent, ftlQuantum_tier_O2dag]
  exact Or.inr rfl

/-- The tachyon is NOT causally consistent. -/
theorem tachyon_not_causally_consistent : ¬ is_causally_consistent ftlTachyon := by
  rw [is_causally_consistent, ftlTachyon_tier_O0]
  intro h; cases h with
  | inl h0 => exact absurd h0 (by decide)
  | inr h0 => exact absurd h0 (by decide)

-- §6  WHAT "FTL TRAVEL" MEANS

/--
The grammar reveals that "FTL travel" is not a speed but a structural
promotion. Light (the photon) IS the critical point Φ_c = ⊙. "Faster
than light" means "structurally beyond the critical point."

Three interpretations:
  1. TACHYON: Φ_c → Φ_super. Drops to O_0. Causal paradox. Unstable.
  2. WORMHOLE: Ω_0 → Ω_Z, T_network → T_bowtie. Reaches O_2†. Consistent.
  3. QUANTUM (ER=EPR): Ω_0 → Ω_Z, P_pm → P_psi. Reaches O_2†. Consistent.

The photon itself can never be FTL. The photon IS the definition of the
critical boundary. FTL requires promotion — changing what the system IS.
-/

-- §7  THE PHOTON IS THE FIXED POINT

/-- Photon and wormhole share Φ_c (criticality) — the light cone boundary. -/
theorem photon_wormhole_share_Phi_c :
    photon.crit = ftlWormhole.crit := by
  rfl

/-- Photon and wormhole share K_fast (driven kinetics / lightspeed). -/
theorem photon_wormhole_share_K_fast :
    photon.kin = ftlWormhole.kin := by
  rfl

/-- Photon and tachyon share K_fast (both travel at the speed limit). -/
theorem photon_tachyon_share_K_fast :
    photon.kin = ftlTachyon.kin := by
  rfl

/-- Photon and tachyon differ at Φ: photon is Φ_c, tachyon is Φ_super. -/
theorem photon_tachyon_differ_at_Phi :
    photon.crit ≠ ftlTachyon.crit := by
  native_decide

/-- Photon and quantum share Φ_c. -/
theorem photon_quantum_share_Phi_c :
    photon.crit = ftlQuantum.crit := by
  rfl

/-- Photon and quantum share K_fast. -/
theorem photon_quantum_share_K_fast :
    photon.kin = ftlQuantum.kin := by
  rfl

/--
The photon kernel theorem: Φ_c and K_fast are invariant across all FTL
variants except the tachyon (which changes Φ_c → Φ_super). Wormhole and
quantum variants preserve both. The photon IS the critical kernel.
-/
theorem photon_kernel_invariant :
    (photon.crit = ftlWormhole.crit ∧ photon.kin = ftlWormhole.kin) ∧
    (photon.crit = ftlQuantum.crit  ∧ photon.kin = ftlQuantum.kin)  ∧
    (photon.kin  = ftlTachyon.kin) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

-- §8  STRUCTURAL INTERPRETATION OF THE SPEED OF LIGHT

/--
The grammar's answer to "why c?":

The speed of light c is not a fundamental constant of nature in the
usual sense. It is the structural consequence of the photon sitting at
Φ_c (criticality) with K_fast (driven kinetics) and Ω_0 (no topological
protection).

Φ_c means: the system is at the critical point — the boundary between
timelike and spacelike. Masslessness IS criticality.

K_fast means: the system has no internal clock (τ ≪ T_obs). This is
why photons experience no proper time.

Ω_0 means: U(1) is abelian — no self-interaction, no winding. This is
why photons don't scatter in vacuum.

Together: Φ_c + K_fast + Ω_0 = the structural definition of "travels
at the invariant maximum speed." This speed is invariant because it
is determined by structure (π₁), not magnitude (π₂).
-/

end Imscribing.Paraconsistent.FTLTravel