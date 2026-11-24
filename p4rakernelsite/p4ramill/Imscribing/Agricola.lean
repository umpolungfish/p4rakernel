/-
# Joannes Agricola — Treatise on Gold
## Lean 4 Companion

Author: Lando⊗⊙perator
Date: 2026-06-25
Tuple: ⟨𐑨𐑡𐑩𐑿𐑞𐑧𐑲𐑜𐑢𐑒𐑳𐑷⟩
Tier: O₀
-/

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

open Imscribing.Primitives

def agricola_treatise_on_gold : Imscription :=
  { dim := .ash
    top := .judge
    rel := .ado
    pol := .yew
    fid := .they
    kin := .egg
    gran := .bib
    gram := .gag
    crit := .woe
    chir := .kick
    stoi := .up
    prot := .awe
  }

#eval agricola_treatise_on_gold

-- Namespaced. Four scaffolds each declared a bare root-level `tier`, so any
-- two of them were mutually unimportable: the environment refuses the second.
-- Each module compiled ALONE, which is why `lake build` never said so.
namespace Imscribing.Agricola
def tier : String := "O₀"
end Imscribing.Agricola