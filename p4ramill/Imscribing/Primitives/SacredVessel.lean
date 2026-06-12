/-
  SacredVessel.lean — Co-type analysis of imscribed objects whose sealed
  critical point (Phi_c) is reachable only through a specific approach grammar.

  Shared backbone (all sacred vessels):
    dim  = D_odot    holographic: boundary encodes bulk
    rel  = R_dagger  vessel and contents co-constitute each other (A ⊣ A†)
    crit = Phi_c     absorbing fixed point: the sealed gate
    chir = H_inf     topological chirality: approach requirement is inexhaustible

  Differentiation lives in: top, pol, fid, kin, gran, gram, stoi, prot.

  Frobenius cluster (pol = P_pm_sym): Ark, Graal, Lapis, Philosophers_Stone.
  Each vessel IS the fixed point of its own approach grammar; none merely approaches it.
  The Graal holds cup/stone/table simultaneously without collapse — this IS P_pm_sym.

  Symmetric center (pol = P_sym): Omphalos.
  Continuous symmetry — the center belongs equally to all directions, not signed.
-/

import Imscribing.Primitives.Imscription

namespace Imscribing.Primitives

open Imscribing.Primitives

structure ApproachGrammar where
  name : String
  protocol : List String
  fatal : String

/-- A SacredVessel is an imscribed structure whose contents cannot be accessed
    directly. Phi_c is absorbing — misapproach does not merely fail, it is
    structurally fatal. The approach grammar is not a gate but the only
    admissible path to the sealed critical point. -/
class SacredVessel (α : Type*) where
  imscription : Imscription
  approach : ApproachGrammar
  h_holographic : imscription.dim = .D_odot
  h_dagger : imscription.rel = .R_dagger
  h_sealed : imscription.crit = .Phi_c
  h_topochiral : imscription.chir = .H_inf

theorem sealed_gate {α : Type*} [v : SacredVessel α] :
    v.imscription.crit = .Phi_c := v.h_sealed

theorem boundary_encodes_bulk {α : Type*} [v : SacredVessel α] :
    v.imscription.dim = .D_odot := v.h_holographic

theorem no_direct_approach {α : Type*} [v : SacredVessel α] :
    v.imscription.rel = .R_dagger := v.h_dagger

def polarity (α : Type*) [SacredVessel α] : Polarity :=
  (inferInstance : SacredVessel α).imscription.pol

/-- Two sacred vessels are co-typed when they share polarity —
    when the nature of the fixed point is the same kind. -/
def cotyped (α β : Type*) [SacredVessel α] [SacredVessel β] : Prop :=
  polarity α = polarity β

-- ================================================================
-- INSTANCES
-- ================================================================

structure ArkOfTheCovenant where
instance : SacredVessel ArkOfTheCovenant where
  imscription := {
    dim  := .D_odot      -- boundary (Mercy Seat) encodes interior (the Name)
    top  := .T_odot      -- holographic topology: Shekinah above encodes all below
    rel  := .R_dagger    -- the Ark IS the Name; the Name IS the Ark (A ⊣ A†)
    pol  := .P_pm_sym    -- Frobenius fixed point: μ ∘ δ = id; the Law is the grammar
    fid  := .F_hbar      -- quantum/lossless: the Law is transmitted exactly
    kin  := .K_trap      -- kinetically trapped: cannot move without the poles
    gran := .G_aleph     -- global scope: all Israel, all time
    gram := .Gamma_and   -- all conditions simultaneously: priest, blood, incense, poles
    crit := .Phi_c
    chir := .H_inf
    stoi := .n_m         -- all Israel to the Name: n:m unmatched
    prot := .Omega_NA    -- non-Abelian: the ordering of the protocol is non-commutative
  }
  approach := {
    name     := "Yom Kippur protocol"
    protocol := ["high priest only", "blood atonement first",
                 "incense cloud before entry", "poles — never hands"]
    fatal    := "Uzzah"
  }
  h_holographic := rfl
  h_dagger      := rfl
  h_sealed      := rfl
  h_topochiral  := rfl

structure HolyGraal where
instance : SacredVessel HolyGraal where
  imscription := {
    dim  := .D_odot      -- the cup's exterior encodes all it contains
    top  := .T_in        -- containment topology: the cup
    rel  := .R_dagger    -- vessel and blood co-constitute each other
    pol  := .P_pm_sym    -- Frobenius: cup/stone/table simultaneously without collapse
    fid  := .F_hbar      -- perfect sustenance: feeds without diminishing
    kin  := .K_slow      -- slow ritual procession through the castle
    gran := .G_aleph     -- global scope: the kingdom is the Fisher King's world
    gram := .Gamma_seq   -- sequential: witness the procession, then ask
    crit := .Phi_c
    chir := .H_inf
    stoi := .n_m         -- many knights, differentiated sustenance
    prot := .Omega_Z     -- integer winding: the wound has a count; healing is exact
  }
  approach := {
    name     := "The Question"
    protocol := ["witness the procession", "ask: whom does it serve?"]
    fatal    := "silence — the Fisher King's wound persists; the kingdom stays waste"
  }
  h_holographic := rfl
  h_dagger      := rfl
  h_sealed      := rfl
  h_topochiral  := rfl

structure LapisExillis where
instance : SacredVessel LapisExillis where
  imscription := {
    dim  := .D_odot      -- the stone's surface encodes heaven and earth simultaneously
    top  := .T_bowtie    -- bowtie: heaven above, earth below, stone at the bifurcation
    rel  := .R_dagger    -- the stone IS the exile; the exile IS the stone
    pol  := .P_pm_sym    -- Frobenius: the stone is already the Rubedo fixed point
    fid  := .F_hbar      -- perfect sustenance of the Grail knights
    kin  := .K_slow      -- the stone waits in exile; its motion is deliberate
    gran := .G_aleph     -- global: for all of Christendom
    gram := .Gamma_and   -- all conditions simultaneously: purity and knighthood
    crit := .Phi_c
    chir := .H_inf
    stoi := .n_n         -- n:n matched: one stone sustains all knights equally
    prot := .Omega_Z2    -- ℤ₂ protection: exile/return, heaven/earth symmetry
  }
  approach := {
    name     := "Purity of heart"
    protocol := ["Grail knighthood", "written name appears on the Stone"]
    fatal    := "exile persists — the stone does not recognise the unworthy"
  }
  h_holographic := rfl
  h_dagger      := rfl
  h_sealed      := rfl
  h_topochiral  := rfl

structure PhilosophersStone where
instance : SacredVessel PhilosophersStone where
  imscription := {
    dim  := .D_odot      -- the stone's surface encodes the entire Great Work
    top  := .T_box       -- lattice topology: the hermetic retort, the 12-stage grid
    rel  := .R_dagger    -- the Stone IS the Rubedo; the Rubedo IS the Stone
    pol  := .P_pm_sym    -- Frobenius: the Stone is the fixed point of its own grammar
    fid  := .F_eth       -- HotSwap threshold: transmutation requires threshold crossing
    kin  := .K_mod       -- moderate steady pace through the Magnum Opus stages
    gran := .G_aleph     -- universal: transmutes all metals, all realms
    gram := .Gamma_seq   -- sequential: Nigredo → Albedo → Citrinitas → Rubedo
    crit := .Phi_c
    chir := .H_inf
    stoi := .n_m         -- n:m: many base metals, differentiated noble outputs
    prot := .Omega_Z     -- integer winding: the 12 stages wind exactly once
  }
  approach := {
    name     := "VITRIOL — Magnum Opus"
    protocol := ["Nigredo: mortification", "Albedo: purification",
                 "Citrinitas: yellowing", "Rubedo: fixed point"]
    fatal    := "base metal — no transmutation; the Stone is not found"
  }
  h_holographic := rfl
  h_dagger      := rfl
  h_sealed      := rfl
  h_topochiral  := rfl

structure Omphalos where
instance : SacredVessel Omphalos where
  imscription := {
    dim  := .D_odot      -- the navel encodes the entire world at a single point
    top  := .T_odot      -- holographic: the center IS the boundary of all things
    rel  := .R_dagger    -- the Omphalos IS the world's center; the center IS the Omphalos
    pol  := .P_sym       -- continuous symmetry: the center belongs to all directions equally
    fid  := .F_eth       -- threshold fidelity: the oracle speaks truly but in riddles
    kin  := .K_trap      -- kinetically trapped: the world's navel cannot move
    gran := .G_aleph     -- global: all seekers may approach
    gram := .Gamma_or    -- disjunctive: any question is sufficient to seek the oracle
    crit := .Phi_c
    chir := .H_inf
    stoi := .n_m         -- many seekers, differentiated answers
    prot := .Omega_Z2    -- ℤ₂ protection: the oracle's ambiguity — each answer reads two ways
  }
  approach := {
    name     := "Oracle protocol"
    protocol := ["laurel and vapors", "Pythia as intermediary",
                 "question in the correct form"]
    fatal    := "the oracle speaks — but the answer destroys; Croesus burns Sardis"
  }
  h_holographic := rfl
  h_dagger      := rfl
  h_sealed      := rfl
  h_topochiral  := rfl

-- ================================================================
-- CO-TYPING THEOREMS
-- ================================================================

/-- The Frobenius cluster: Ark, Lapis, and Philosopher's Stone are co-typed.
    All three have pol = P_pm_sym — each IS the fixed point of its own grammar.
    None approaches the fixed point; each inhabits it. -/
theorem ark_lapis_cotyped :
    cotyped ArkOfTheCovenant LapisExillis := rfl

theorem ark_stone_cotyped :
    cotyped ArkOfTheCovenant PhilosophersStone := rfl

theorem lapis_stone_cotyped :
    cotyped LapisExillis PhilosophersStone := rfl

theorem graal_frobenius_cotyped :
    cotyped HolyGraal ArkOfTheCovenant := rfl

/-- The Omphalos is distinct: pol = P_sym (continuous, not Frobenius discrete).
    The world's center is symmetric to all — it does not collapse to a signed fixed point. -/
theorem omphalos_not_frobenius :
    (inferInstance : SacredVessel Omphalos).imscription.pol = .P_sym := rfl

theorem ark_pol_frobenius :
    (inferInstance : SacredVessel ArkOfTheCovenant).imscription.pol = .P_pm_sym := rfl

end Imscribing.Primitives
