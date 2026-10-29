-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⊤ → ⋈ → ⊙ → ≻ → ⊤ → ∈ → ≻ → ⊤ → ⋈ → ⊙ → ⊡ → ≺ → ⊥ → ≻ → ⊤ → ⊞ → ⋈ → ⊙ → ∈ → ≺ → ⊥ → ≻ → ⊤ → ⊞ → ∋ → ⊡ → ∋ → ⊡ → ≻ → ⊤ → ⋈ → ⊙ → ≻ → ≺ → ⊥ → ∋ → ⊡ → ⊣
-- Class: elemental_carbon
-- Fingerprint: sig=(21,5,11,4)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=41
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(21, 27), (8, 29)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [6] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [7] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [8] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [10] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [11] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [12] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [13] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [14] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [15] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [16] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [17] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [18] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [19] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [20] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [21] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [22] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [23] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [24] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [25] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [26] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [27] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [28] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [29] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [30] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [33] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [34] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [35] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [36] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [37] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [38] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [39] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [40] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def elemental_carbon_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def elemental_carbon_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l9 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l16 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l24 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l35 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def elemental_carbon_protocol : IGProtocol elemental_carbon_initial elemental_carbon_s40 :=
  .withGram Grammar.measure <|
  (.seq (.arrow elemental_carbon_l0 elemental_carbon_initial elemental_carbon_s0) (.seq (.arrow elemental_carbon_l1 elemental_carbon_s0 elemental_carbon_s1) (.seq (.arrow elemental_carbon_l2 elemental_carbon_s1 elemental_carbon_s2) (.seq (.arrow elemental_carbon_l3 elemental_carbon_s2 elemental_carbon_s3) (.seq (.arrow elemental_carbon_l4 elemental_carbon_s3 elemental_carbon_s4) (.seq (.arrow elemental_carbon_l5 elemental_carbon_s4 elemental_carbon_s5) (.seq (.arrow elemental_carbon_l6 elemental_carbon_s5 elemental_carbon_s6) (.seq (.arrow elemental_carbon_l7 elemental_carbon_s6 elemental_carbon_s7) (.seq (.arrow elemental_carbon_l8 elemental_carbon_s7 elemental_carbon_s8) (.seq (.prod (.seq (.arrow elemental_carbon_l9 elemental_carbon_s8 elemental_carbon_s9) (.seq (.arrow elemental_carbon_l10 elemental_carbon_s9 elemental_carbon_s10) (.seq (.arrow elemental_carbon_l11 elemental_carbon_s10 elemental_carbon_s11) (.seq (.arrow elemental_carbon_l12 elemental_carbon_s11 elemental_carbon_s12) (.seq (.arrow elemental_carbon_l13 elemental_carbon_s12 elemental_carbon_s13) (.arrow elemental_carbon_l14 elemental_carbon_s13 elemental_carbon_s14)))))) (.seq (.arrow elemental_carbon_l15 elemental_carbon_s8 elemental_carbon_s15) (.seq (.arrow elemental_carbon_l16 elemental_carbon_s15 elemental_carbon_s16) (.seq (.arrow elemental_carbon_l17 elemental_carbon_s16 elemental_carbon_s17) (.seq (.arrow elemental_carbon_l18 elemental_carbon_s17 elemental_carbon_s18) (.seq (.arrow elemental_carbon_l19 elemental_carbon_s18 elemental_carbon_s19) (.seq (.arrow elemental_carbon_l20 elemental_carbon_s19 elemental_carbon_s20) (.seq (.arrow elemental_carbon_l21 elemental_carbon_s20 elemental_carbon_s21) (.seq (.prod (.seq (.arrow elemental_carbon_l25 elemental_carbon_s21 elemental_carbon_s25) (.arrow elemental_carbon_l26 elemental_carbon_s25 elemental_carbon_s26)) (.seq (.arrow elemental_carbon_l22 elemental_carbon_s21 elemental_carbon_s22) (.seq (.arrow elemental_carbon_l23 elemental_carbon_s22 elemental_carbon_s23) (.arrow elemental_carbon_l24 elemental_carbon_s23 elemental_carbon_s24)))) (.seq (.arrow elemental_carbon_l27 (tensorProduct elemental_carbon_s26 elemental_carbon_s24) elemental_carbon_s27) (.arrow elemental_carbon_l28 elemental_carbon_s27 elemental_carbon_s28))))))))))) (.seq (.arrow elemental_carbon_l29 (tensorProduct elemental_carbon_s14 elemental_carbon_s28) elemental_carbon_s29) (.seq (.arrow elemental_carbon_l30 elemental_carbon_s29 elemental_carbon_s30) (.seq (.arrow elemental_carbon_l31 elemental_carbon_s30 elemental_carbon_s31) (.seq (.arrow elemental_carbon_l32 elemental_carbon_s31 elemental_carbon_s32) (.seq (.arrow elemental_carbon_l33 elemental_carbon_s32 elemental_carbon_s33) (.seq (.arrow elemental_carbon_l34 elemental_carbon_s33 elemental_carbon_s34) (.seq (.arrow elemental_carbon_l35 elemental_carbon_s34 elemental_carbon_s35) (.seq (.arrow elemental_carbon_l36 elemental_carbon_s35 elemental_carbon_s36) (.seq (.arrow elemental_carbon_l37 elemental_carbon_s36 elemental_carbon_s37) (.seq (.arrow elemental_carbon_l38 elemental_carbon_s37 elemental_carbon_s38) (.seq (.arrow elemental_carbon_l39 elemental_carbon_s38 elemental_carbon_s39) (.arrow elemental_carbon_l40 elemental_carbon_s39 elemental_carbon_s40))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def elemental_carbon_true_arm : IGProtocol elemental_carbon_initial elemental_carbon_s40 :=
  (elemental_carbon_protocol).restrictToEVALT

-- false arm
noncomputable def elemental_carbon_false_arm : IGProtocol elemental_carbon_initial elemental_carbon_s40 :=
  (elemental_carbon_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def elemental_carbon_tier_ground : OuroboricityTier := TierFunctor.obj elemental_carbon_initial
def elemental_carbon_tier : OuroboricityTier := TierFunctor.obj elemental_carbon_s40
#eval elemental_carbon_tier_ground  -- tier of the ground (pre-transformation)
#eval elemental_carbon_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem elemental_carbon_frobenius :
    igFrobeniusAlg.mul elemental_carbon_initial elemental_carbon_initial = elemental_carbon_initial :=
  igFrobAlg_self_fusion elemental_carbon_initial

theorem elemental_carbon_protocol_depth :
    elemental_carbon_protocol.depth = 33 := by rfl

end Imscribing