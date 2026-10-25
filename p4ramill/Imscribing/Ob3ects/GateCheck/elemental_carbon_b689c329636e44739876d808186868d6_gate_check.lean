-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⋈ → ⊤ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⊥ → ≺ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⋈ → ⊙ → ⊡ → ⊙ → ⊤ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ≻ → ⊙ → ⊤ → ⋈ → ⊡ → ⊙ → ⊤ → ≻ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊤ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊡ → ≺ → ⊥ → ⊡ → ∋ → ⊣
-- Class: elemental_carbon
-- Fingerprint: sig=(49,2,26,14)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=91
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 89)]

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
--   [3] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [7] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [14] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [15] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [16] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [17] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [18] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [19] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [20] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [21] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [22] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [23] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [24] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [25] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [26] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [27] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [28] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [33] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [34] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [35] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [36] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [37] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [38] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [39] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [40] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [41] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [42] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [43] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [44] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [45] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [46] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [47] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [48] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [49] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [52] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [53] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [54] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [55] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [56] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [57] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [58] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [59] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [60] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [61] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [62] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [63] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [64] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [65] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [66] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [67] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [68] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [69] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [70] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [71] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [72] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [73] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [74] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [75] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [76] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [77] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [78] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [79] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [80] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [81] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [82] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [83] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [84] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [85] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [86] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [87] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [88] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [89] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [90] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

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
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_carbon_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_carbon_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_carbon_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_carbon_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_carbon_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
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
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_carbon_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_carbon_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def elemental_carbon_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l17 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l25 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l38 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l47 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l55 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l61 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l68 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_carbon_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l75 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l81 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l82 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l84 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_carbon_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_carbon_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_carbon_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def elemental_carbon_protocol : IGProtocol elemental_carbon_initial elemental_carbon_s90 :=
  .withGram Grammar.measure <|
  (.seq (.arrow elemental_carbon_l0 elemental_carbon_initial elemental_carbon_s0) (.seq (.arrow elemental_carbon_l1 elemental_carbon_s0 elemental_carbon_s1) (.seq (.arrow elemental_carbon_l2 elemental_carbon_s1 elemental_carbon_s2) (.seq (.arrow elemental_carbon_l3 elemental_carbon_s2 elemental_carbon_s3) (.seq (.arrow elemental_carbon_l4 elemental_carbon_s3 elemental_carbon_s4) (.seq (.prod (.seq (.arrow elemental_carbon_l5 elemental_carbon_s4 elemental_carbon_s5) (.seq (.arrow elemental_carbon_l6 elemental_carbon_s5 elemental_carbon_s6) (.seq (.arrow elemental_carbon_l7 elemental_carbon_s6 elemental_carbon_s7) (.seq (.arrow elemental_carbon_l8 elemental_carbon_s7 elemental_carbon_s8) (.seq (.arrow elemental_carbon_l9 elemental_carbon_s8 elemental_carbon_s9) (.seq (.arrow elemental_carbon_l10 elemental_carbon_s9 elemental_carbon_s10) (.seq (.arrow elemental_carbon_l11 elemental_carbon_s10 elemental_carbon_s11) (.seq (.arrow elemental_carbon_l12 elemental_carbon_s11 elemental_carbon_s12) (.arrow elemental_carbon_l13 elemental_carbon_s12 elemental_carbon_s13))))))))) (.seq (.arrow elemental_carbon_l14 elemental_carbon_s4 elemental_carbon_s14) (.seq (.arrow elemental_carbon_l15 elemental_carbon_s14 elemental_carbon_s15) (.seq (.arrow elemental_carbon_l16 elemental_carbon_s15 elemental_carbon_s16) (.seq (.arrow elemental_carbon_l17 elemental_carbon_s16 elemental_carbon_s17) (.seq (.arrow elemental_carbon_l18 elemental_carbon_s17 elemental_carbon_s18) (.seq (.arrow elemental_carbon_l19 elemental_carbon_s18 elemental_carbon_s19) (.seq (.arrow elemental_carbon_l20 elemental_carbon_s19 elemental_carbon_s20) (.seq (.arrow elemental_carbon_l21 elemental_carbon_s20 elemental_carbon_s21) (.seq (.arrow elemental_carbon_l22 elemental_carbon_s21 elemental_carbon_s22) (.seq (.arrow elemental_carbon_l23 elemental_carbon_s22 elemental_carbon_s23) (.seq (.arrow elemental_carbon_l24 elemental_carbon_s23 elemental_carbon_s24) (.seq (.arrow elemental_carbon_l25 elemental_carbon_s24 elemental_carbon_s25) (.seq (.arrow elemental_carbon_l26 elemental_carbon_s25 elemental_carbon_s26) (.seq (.arrow elemental_carbon_l27 elemental_carbon_s26 elemental_carbon_s27) (.seq (.arrow elemental_carbon_l28 elemental_carbon_s27 elemental_carbon_s28) (.seq (.arrow elemental_carbon_l29 elemental_carbon_s28 elemental_carbon_s29) (.seq (.arrow elemental_carbon_l30 elemental_carbon_s29 elemental_carbon_s30) (.seq (.arrow elemental_carbon_l31 elemental_carbon_s30 elemental_carbon_s31) (.seq (.arrow elemental_carbon_l32 elemental_carbon_s31 elemental_carbon_s32) (.seq (.arrow elemental_carbon_l33 elemental_carbon_s32 elemental_carbon_s33) (.seq (.arrow elemental_carbon_l34 elemental_carbon_s33 elemental_carbon_s34) (.seq (.arrow elemental_carbon_l35 elemental_carbon_s34 elemental_carbon_s35) (.seq (.arrow elemental_carbon_l36 elemental_carbon_s35 elemental_carbon_s36) (.seq (.arrow elemental_carbon_l37 elemental_carbon_s36 elemental_carbon_s37) (.seq (.arrow elemental_carbon_l38 elemental_carbon_s37 elemental_carbon_s38) (.seq (.arrow elemental_carbon_l39 elemental_carbon_s38 elemental_carbon_s39) (.seq (.arrow elemental_carbon_l40 elemental_carbon_s39 elemental_carbon_s40) (.seq (.arrow elemental_carbon_l41 elemental_carbon_s40 elemental_carbon_s41) (.seq (.arrow elemental_carbon_l42 elemental_carbon_s41 elemental_carbon_s42) (.seq (.arrow elemental_carbon_l43 elemental_carbon_s42 elemental_carbon_s43) (.seq (.arrow elemental_carbon_l44 elemental_carbon_s43 elemental_carbon_s44) (.seq (.arrow elemental_carbon_l45 elemental_carbon_s44 elemental_carbon_s45) (.seq (.arrow elemental_carbon_l46 elemental_carbon_s45 elemental_carbon_s46) (.seq (.arrow elemental_carbon_l47 elemental_carbon_s46 elemental_carbon_s47) (.seq (.arrow elemental_carbon_l48 elemental_carbon_s47 elemental_carbon_s48) (.seq (.arrow elemental_carbon_l49 elemental_carbon_s48 elemental_carbon_s49) (.seq (.arrow elemental_carbon_l50 elemental_carbon_s49 elemental_carbon_s50) (.seq (.arrow elemental_carbon_l51 elemental_carbon_s50 elemental_carbon_s51) (.seq (.arrow elemental_carbon_l52 elemental_carbon_s51 elemental_carbon_s52) (.seq (.arrow elemental_carbon_l53 elemental_carbon_s52 elemental_carbon_s53) (.seq (.arrow elemental_carbon_l54 elemental_carbon_s53 elemental_carbon_s54) (.seq (.arrow elemental_carbon_l55 elemental_carbon_s54 elemental_carbon_s55) (.seq (.arrow elemental_carbon_l56 elemental_carbon_s55 elemental_carbon_s56) (.seq (.arrow elemental_carbon_l57 elemental_carbon_s56 elemental_carbon_s57) (.seq (.arrow elemental_carbon_l58 elemental_carbon_s57 elemental_carbon_s58) (.seq (.arrow elemental_carbon_l59 elemental_carbon_s58 elemental_carbon_s59) (.seq (.arrow elemental_carbon_l60 elemental_carbon_s59 elemental_carbon_s60) (.seq (.arrow elemental_carbon_l61 elemental_carbon_s60 elemental_carbon_s61) (.seq (.arrow elemental_carbon_l62 elemental_carbon_s61 elemental_carbon_s62) (.seq (.arrow elemental_carbon_l63 elemental_carbon_s62 elemental_carbon_s63) (.seq (.arrow elemental_carbon_l64 elemental_carbon_s63 elemental_carbon_s64) (.seq (.arrow elemental_carbon_l65 elemental_carbon_s64 elemental_carbon_s65) (.seq (.arrow elemental_carbon_l66 elemental_carbon_s65 elemental_carbon_s66) (.seq (.arrow elemental_carbon_l67 elemental_carbon_s66 elemental_carbon_s67) (.seq (.arrow elemental_carbon_l68 elemental_carbon_s67 elemental_carbon_s68) (.seq (.arrow elemental_carbon_l69 elemental_carbon_s68 elemental_carbon_s69) (.seq (.arrow elemental_carbon_l70 elemental_carbon_s69 elemental_carbon_s70) (.seq (.arrow elemental_carbon_l71 elemental_carbon_s70 elemental_carbon_s71) (.seq (.arrow elemental_carbon_l72 elemental_carbon_s71 elemental_carbon_s72) (.seq (.arrow elemental_carbon_l73 elemental_carbon_s72 elemental_carbon_s73) (.seq (.arrow elemental_carbon_l74 elemental_carbon_s73 elemental_carbon_s74) (.seq (.arrow elemental_carbon_l75 elemental_carbon_s74 elemental_carbon_s75) (.seq (.arrow elemental_carbon_l76 elemental_carbon_s75 elemental_carbon_s76) (.seq (.arrow elemental_carbon_l77 elemental_carbon_s76 elemental_carbon_s77) (.seq (.arrow elemental_carbon_l78 elemental_carbon_s77 elemental_carbon_s78) (.seq (.arrow elemental_carbon_l79 elemental_carbon_s78 elemental_carbon_s79) (.seq (.arrow elemental_carbon_l80 elemental_carbon_s79 elemental_carbon_s80) (.seq (.arrow elemental_carbon_l81 elemental_carbon_s80 elemental_carbon_s81) (.seq (.arrow elemental_carbon_l82 elemental_carbon_s81 elemental_carbon_s82) (.seq (.arrow elemental_carbon_l83 elemental_carbon_s82 elemental_carbon_s83) (.seq (.arrow elemental_carbon_l84 elemental_carbon_s83 elemental_carbon_s84) (.seq (.arrow elemental_carbon_l85 elemental_carbon_s84 elemental_carbon_s85) (.seq (.arrow elemental_carbon_l86 elemental_carbon_s85 elemental_carbon_s86) (.seq (.arrow elemental_carbon_l87 elemental_carbon_s86 elemental_carbon_s87) (.arrow elemental_carbon_l88 elemental_carbon_s87 elemental_carbon_s88)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow elemental_carbon_l89 (tensorProduct elemental_carbon_s13 elemental_carbon_s88) elemental_carbon_s89) (.arrow elemental_carbon_l90 elemental_carbon_s89 elemental_carbon_s90))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def elemental_carbon_true_arm : IGProtocol elemental_carbon_initial elemental_carbon_s90 :=
  (elemental_carbon_protocol).restrictToEVALT

-- false arm
noncomputable def elemental_carbon_false_arm : IGProtocol elemental_carbon_initial elemental_carbon_s90 :=
  (elemental_carbon_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def elemental_carbon_tier_ground : OuroboricityTier := TierFunctor.obj elemental_carbon_initial
def elemental_carbon_tier : OuroboricityTier := TierFunctor.obj elemental_carbon_s90
#eval elemental_carbon_tier_ground  -- tier of the ground (pre-transformation)
#eval elemental_carbon_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem elemental_carbon_frobenius :
    igFrobeniusAlg.mul elemental_carbon_initial elemental_carbon_initial = elemental_carbon_initial :=
  igFrobAlg_self_fusion elemental_carbon_initial

theorem elemental_carbon_protocol_depth :
    elemental_carbon_protocol.depth = 82 := by rfl

end Imscribing