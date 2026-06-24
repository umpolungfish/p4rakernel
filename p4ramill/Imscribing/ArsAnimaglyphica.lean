/-
Ars Animaglyphica — Animal Morphological Imscription
Lean 4 Formalization — 14 canonical animal types.

4 invariants (D, R, Phi, f), 8 discriminants (T, C, Gamma, G, Phi_c, H, Sigma, Omega).
Auto-generated from types.py. All invariant theorems proved by `decide`.

Author: Lando⊗⊙perator
-/

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

open Imscribing.Primitives


namespace ArsAnimaglyphica

-- ═══════════════════════════════════════════════════════════════
-- 14 CANONICAL ANIMAL IMSCRIPTIONS
-- ═══════════════════════════════════════════════════════════════

-- Type 1: Ophidian Venom [O2_dagger] 
def ophidian_venom : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.so
    Protection.oak

-- Type 2: Amphibian Dermal [O2] 
def amphibian_dermal : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.are
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.egg
    Granularity.ice
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

-- Type 3: Arthropod Exoskeletal [O2] 
def arthropod_exoskeletal : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.oil
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

-- Type 4: Molluscan Harpoon [O2_dagger] 
def molluscan_harpoon : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.so
    Protection.oak

-- Type 5: Marine Sessile Defense [O1] 
def marine_sessile_defense : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.mime
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.on
    Granularity.ice
    Grammar.measure
    Criticality.woe
    Chirality.wool
    Stoichiometry.up
    Protection.awe

-- Type 6: Mammalian Glandular [O1] 
def mammalian_glandular : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.egg
    Granularity.ice
    Grammar.measure
    Criticality.woe
    Chirality.sure
    Stoichiometry.hung
    Protection.awe

-- Type 7: Fish Structural [O1] 
def fish_structural : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.are
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.egg
    Granularity.ice
    Grammar.ooze
    Criticality.woe
    Chirality.sure
    Stoichiometry.hung
    Protection.awe

-- Type 8: Hymenopteran Venom [O2] 
def hymenopteran_venom : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.ooze
    Criticality.monad
    Chirality.sure
    Stoichiometry.up
    Protection.ah

-- Type 9: Annelid Anticoagulant [O1] 
def annelid_anticoagulant : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.woe
    Chirality.wool
    Stoichiometry.so
    Protection.awe

-- Type 10: Cephalopod Ink [O2] 
def cephalopod_ink : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.ice
    Grammar.ooze
    Criticality.monad
    Chirality.kick
    Stoichiometry.so
    Protection.awe

-- Type 11: Echinoderm Regenerative [O2] 
def echinoderm_regenerative : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.are
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.egg
    Granularity.ice
    Grammar.ooze
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

-- Type 12: Cnidarian Nematocyst [O2_dagger] 
def cnidarian_nematocyst : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.mime
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.so
    Protection.oak

-- Type 13: Avian Preen [O1] 
def avian_preen : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.eat
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.egg
    Granularity.ice
    Grammar.measure
    Criticality.woe
    Chirality.sure
    Stoichiometry.hung
    Protection.awe

-- Type 14: Reptilian Oral [O2] 
def reptilian_oral : Imscription :=
  Imscription.mk Dimensionality.if'
    Topology.judge
    Relational.ian
    Polarity.nun
    Fidelity.they
    KineticChar.air
    Granularity.bib
    Grammar.measure
    Criticality.monad
    Chirality.wool
    Stoichiometry.up
    Protection.ah

-- ═══════════════════════════════════════════════════════════════
-- TYPE LIST AND INVARIANT THEOREMS (proved by decide)
-- ═══════════════════════════════════════════════════════════════

def all_animal_types : List Imscription :=
  [ophidian_venom, amphibian_dermal, arthropod_exoskeletal, molluscan_harpoon, marine_sessile_defense, mammalian_glandular, fish_structural, hymenopteran_venom, annelid_anticoagulant, cephalopod_ink, echinoderm_regenerative, cnidarian_nematocyst, avian_preen, reptilian_oral]

-- All medicinal animals share D=Dimensionality.if' 
theorem invariant_D : ∀ (f : Imscription), f ∈ all_animal_types →
    f.dim = Dimensionality.if' := by
  unfold all_animal_types
  decide

-- All medicinal animals share R=Relational.ian 
theorem invariant_R : ∀ (f : Imscription), f ∈ all_animal_types →
    f.rel = Relational.ian := by
  unfold all_animal_types
  decide

-- All medicinal animals share Phi=Polarity.nun 
theorem invariant_Phi : ∀ (f : Imscription), f ∈ all_animal_types →
    f.pol = Polarity.nun := by
  unfold all_animal_types
  decide

-- All medicinal animals share f=Fidelity.they 
theorem invariant_f : ∀ (f : Imscription), f ∈ all_animal_types →
    f.fid = Fidelity.they := by
  unfold all_animal_types
  decide

-- ═══════════════════════════════════════════════════════════════
-- STRUCTURAL DISTANCE THEOREMS
-- ═══════════════════════════════════════════════════════════════

--  
theorem ophidian_molluscan_distance :
    primitiveMismatches ophidian_venom molluscan_harpoon = 1 := by
  unfold ophidian_venom molluscan_harpoon primitiveMismatches
  native_decide

--  
theorem ophidian_hymenopteran_distance :
    primitiveMismatches ophidian_venom hymenopteran_venom = 4 := by
  unfold ophidian_venom hymenopteran_venom primitiveMismatches
  native_decide

--  
theorem marine_annelid_distance :
    primitiveMismatches marine_sessile_defense annelid_anticoagulant = 4 := by
  unfold marine_sessile_defense annelid_anticoagulant primitiveMismatches
  native_decide

--  
theorem mammalian_fish_distance :
    primitiveMismatches mammalian_glandular fish_structural = 2 := by
  unfold mammalian_glandular fish_structural primitiveMismatches
  native_decide

--  
theorem arthropod_hymenopteran_distance :
    primitiveMismatches arthropod_exoskeletal hymenopteran_venom = 3 := by
  unfold arthropod_exoskeletal hymenopteran_venom primitiveMismatches
  native_decide

--  
theorem max_animal_distance :
    primitiveMismatches ophidian_venom fish_structural = 8 := by
  unfold ophidian_venom fish_structural primitiveMismatches
  native_decide

--  
theorem cephalopod_ophidian_distance :
    primitiveMismatches cephalopod_ink ophidian_venom = 5 := by
  unfold cephalopod_ink ophidian_venom primitiveMismatches
  native_decide

--  
theorem echinoderm_amphibian_distance :
    primitiveMismatches echinoderm_regenerative amphibian_dermal = 1 := by
  unfold echinoderm_regenerative amphibian_dermal primitiveMismatches
  native_decide

--  
theorem cnidarian_ophidian_distance :
    primitiveMismatches cnidarian_nematocyst ophidian_venom = 1 := by
  unfold cnidarian_nematocyst ophidian_venom primitiveMismatches
  native_decide

--  
theorem reptilian_ophidian_distance :
    primitiveMismatches reptilian_oral ophidian_venom = 2 := by
  unfold reptilian_oral ophidian_venom primitiveMismatches
  native_decide

--  
theorem avian_mammalian_distance :
    primitiveMismatches avian_preen mammalian_glandular = 0 := by
  unfold avian_preen mammalian_glandular primitiveMismatches
  native_decide

end ArsAnimaglyphica