/-
Ars Fungiglyphica — Fungal Morphological Imscription
Lean 4 Formalization — 15 canonical fungal types.

5 invariants (D, R, Phi, f, Sigma), 7 discriminants (T, C, Gamma, G, Phi_c, H, Omega).
Auto-generated from types.py. All invariant theorems proved by `decide`.

Lean constructor mapping:
  D: if'=𐑦   T: oil=𐑶 mime=𐑥 eat=𐑰 are=𐑸 judge=𐑡
  R: ian=𐑾   Phi: out=𐑬   f: age=𐑱
  C: on=𐑤 egg=𐑧 air=𐑘   Gamma: bib=𐑲 ice=𐑔
  G: ooze=𐑵 measure=𐑠 vow=𐑝   Phi_c: monad=⊙ woe=𐑢
  H: wool=𐑫 sure=𐑖 kick=𐑒   Sigma: up=𐑳
  Omega: oak=𐑴 ah=𐑭 awe=𐑷

Author: Lando⊗⊙perator
-/

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

open Imscribing.Primitives


namespace ArsFungiglyphica

-- ═══════════════════════════════════════════════════════════════
-- 15 CANONICAL FUNGAL IMSCRIPTIONS
-- ═══════════════════════════════════════════════════════════════

/-- Type 1: Bracket Polypore [O2_dagger] --/
def bracket_polypore : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.oil
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.on
    Granularity.bib
    Grammar.ooze
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.oak

/-- Type 2: Tooth Cascade [O2] --/
def tooth_cascade : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.mime
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

/-- Type 3: Entomopathogenic Club [O2] --/
def entomopathogenic_club : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.on
    Granularity.bib
    Grammar.ooze
    Criticality.monad
    Chirality.sure
    Stoichiometry.up
    Protection.ah

/-- Type 4: Gilled Cap-and-Stipe [O2] --/
def gilled_cap_and_stipe : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.are
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.ice
    Grammar.measure
    Criticality.monad
    Chirality.sure
    Stoichiometry.up
    Protection.ah

/-- Type 5: Rosette Cluster [O2] --/
def rosette_cluster : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.ice
    Grammar.ooze
    Criticality.monad
    Chirality.sure
    Stoichiometry.up
    Protection.ah

/-- Type 6: Jelly Gelatinous [O1] --/
def jelly_gelatinous : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.ice
    Grammar.vow
    Criticality.woe
    Chirality.kick
    Stoichiometry.up
    Protection.awe

/-- Type 7: Puffball Spore Sac [O1] --/
def puffball_spore_sac : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.air
    Granularity.bib
    Grammar.ooze
    Criticality.woe
    Chirality.kick
    Stoichiometry.up
    Protection.awe

/-- Type 8: Hypogean Ascomycete [O2] --/
def hypogean_ascomycete : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.kick
    Stoichiometry.up
    Protection.ah

/-- Type 9: Rust Smut Pathogen [O1] --/
def rust_smut_pathogen : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.woe
    Chirality.kick
    Stoichiometry.up
    Protection.awe

/-- Type 10: Lichen Symbiont [O2_dagger] --/
def lichen_symbiont : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.oil
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.on
    Granularity.bib
    Grammar.ooze
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.oak

/-- Type 11: Stinkhorn Emergence [O2] --/
def stinkhorn_emergence : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.mime
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.ice
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

/-- Type 12: Coral Ramaria [O2] --/
def coral_ramaria : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.egg
    Granularity.ice
    Grammar.ooze
    Criticality.monad
    Chirality.sure
    Stoichiometry.up
    Protection.ah

/-- Type 13: Cup Discus [O1] --/
def cup_discus : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.woe
    Chirality.kick
    Stoichiometry.up
    Protection.awe

/-- Type 14: Earthball Globus [O1] --/
def earthball_globus : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.on
    Granularity.bib
    Grammar.ooze
    Criticality.woe
    Chirality.sure
    Stoichiometry.up
    Protection.awe

/-- Type 15: Myxomycete Plasmodium [O2_dagger] --/
def myxomycete_plasmodium : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.out
    Fidelity.age
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.kick
    Stoichiometry.up
    Protection.oak

-- ═══════════════════════════════════════════════════════════════
-- TYPE LIST AND INVARIANT THEOREMS (proved by decide)
-- ═══════════════════════════════════════════════════════════════

def all_fungal_types : List Imscription :=
  [bracket_polypore, tooth_cascade, entomopathogenic_club, gilled_cap_and_stipe, rosette_cluster, jelly_gelatinous, puffball_spore_sac, hypogean_ascomycete, rust_smut_pathogen, lichen_symbiont, stinkhorn_emergence, coral_ramaria, cup_discus, earthball_globus, myxomycete_plasmodium]

/-- All medicinal fungi share D=Dimensionality.if' (imscriptive dimensionality) --/
theorem invariant_D : ∀ (f : Imscription), f ∈ all_fungal_types →
    f.dim = Dimensionality.if' := by
  unfold all_fungal_types
  decide

/-- All medicinal fungi share R=Relational.ian (bidirectional coupling) --/
theorem invariant_R : ∀ (f : Imscription), f ∈ all_fungal_types →
    f.rel = Relational.ian := by
  unfold all_fungal_types
  decide

/-- All medicinal fungi share Phi=Polarity.out (partial parity / Z2) --/
theorem invariant_Phi : ∀ (f : Imscription), f ∈ all_fungal_types →
    f.pol = Polarity.out := by
  unfold all_fungal_types
  decide

/-- All medicinal fungi share f=Fidelity.age (classical fidelity) --/
theorem invariant_f : ∀ (f : Imscription), f ∈ all_fungal_types →
    f.fid = Fidelity.age := by
  unfold all_fungal_types
  decide

/-- All medicinal fungi share Sigma=Stoichiometry.up (heterogeneous stoichiometry) --/
theorem invariant_Sigma : ∀ (f : Imscription), f ∈ all_fungal_types →
    f.stoi = Stoichiometry.up := by
  unfold all_fungal_types
  decide

-- ═══════════════════════════════════════════════════════════════
-- STRUCTURAL DISTANCE THEOREMS
-- ═══════════════════════════════════════════════════════════════

/-- Bracket Polypore and Lichen Symbiont are structurally identical (0 mismatches). --/
theorem bracket_lichen_distance_zero :
    primitiveMismatches bracket_polypore lichen_symbiont = 0 := by
  unfold bracket_polypore lichen_symbiont primitiveMismatches
  native_decide

/-- Stinkhorn Emergence and Tooth Cascade differ only in Gamma (ice vs bib). --/
theorem stinkhorn_tooth_distance :
    primitiveMismatches stinkhorn_emergence tooth_cascade = 1 := by
  unfold stinkhorn_emergence tooth_cascade primitiveMismatches
  native_decide

/-- Myxomycete Plasmodium and Bracket Polypore differ on 5 primitives. --/
theorem myxomycete_bracket_distance :
    primitiveMismatches myxomycete_plasmodium bracket_polypore = 4 := by
  unfold myxomycete_plasmodium bracket_polypore primitiveMismatches
  native_decide

/-- Coral Ramaria and Rosette Cluster are structurally identical (0 mismatches). Both have branching network topology with broadcast immune signaling. --/
theorem coral_rosette_distance_zero :
    primitiveMismatches coral_ramaria rosette_cluster = 0 := by
  unfold coral_ramaria rosette_cluster primitiveMismatches
  native_decide

/-- Cup Discus and Rust Smut Pathogen both use containment+fast+sequential but Cup is O1 tier. --/
theorem cup_rust_distance :
    primitiveMismatches cup_discus rust_smut_pathogen = 1 := by
  unfold cup_discus rust_smut_pathogen primitiveMismatches
  native_decide

/-- Earthball Globus vs Puffball Spore Sac: both spherical enclosed, but Earthball uses frozen-order kinetics. --/
theorem earthball_puffball_distance :
    primitiveMismatches earthball_globus puffball_spore_sac = 2 := by
  unfold earthball_globus puffball_spore_sac primitiveMismatches
  native_decide

/-- Maximum distance: Bracket Polypore (O2+) vs Jelly Gelatinous (O1) = 7 discriminant mismatches. --/
theorem max_fungal_distance_v2 :
    primitiveMismatches bracket_polypore jelly_gelatinous = 7 := by
  unfold bracket_polypore jelly_gelatinous primitiveMismatches
  native_decide

end ArsFungiglyphica