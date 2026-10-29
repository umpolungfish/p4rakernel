-- IGProtocol scaffold: ⊢ → ⊙ → ⊡ → ≻ → ∈ → ⊤ → ≻ → ≺ → ⊥ → ⋈ → ⊙ → ⊡ → ⊙ → ⊤ → ≻ → ⊥ → ≺ → ⊞ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊤ → ≺ → ⋈ → ⊙ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⊥ → ≺ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⊡ → ⊙ → ⋈ → ≻ → ⊤ → ⊥ → ≺ → ⊙ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ≺ → ⊙ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊙ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ≺ → ⊙ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⊞ → ⋈ → ⊡ → ⊙ → ∋ → ⊣
-- Class: the_element_that_is_the_fixed_point_operator_of_the_periodic_horn_torus_of_elements
-- Fingerprint: sig=(61,2,31,16)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=110
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 108)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [3] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [4] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [13] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [14] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [15] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [18] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [19] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [20] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [21] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [22] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [23] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [24] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [25] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [26] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [27] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [28] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [31] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [32] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [33] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [34] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [35] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [36] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [37] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [38] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [39] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [40] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [41] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [42] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [43] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [44] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [45] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [46] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [47] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [48] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [49] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [50] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [51] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [52] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [53] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [55] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [56] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [57] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [58] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [59] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [60] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [61] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [62] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [63] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [64] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [65] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [66] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [67] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [68] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [69] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [70] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [71] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [72] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [73] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [74] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [75] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [76] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [77] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [78] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [79] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [80] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [81] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [82] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [83] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [84] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [85] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [86] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [87] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [88] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [89] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [90] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [91] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [92] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [93] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [94] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [95] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [96] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [97] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [98] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [99] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [100] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [101] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [102] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [103] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [104] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [105] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [106] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [107] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [108] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [109] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_element_that_is_the_fixed_point_921e70_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s100 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s101 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s102 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s103 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s104 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s105 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s106 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s107 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s108 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_s109 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_element_that_is_the_fixed_point_921e70_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l35 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l42 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l51 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l57 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l65 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l73 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l80 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l81 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l82 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l84 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l87 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l91 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l93 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l94 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l95 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l96 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l98 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l100 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l101 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l102 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l103 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l104 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l105 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l106 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_element_that_is_the_fixed_point_921e70_l107 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l108 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_element_that_is_the_fixed_point_921e70_l109 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_element_that_is_the_fixed_point_921e70_protocol : IGProtocol the_element_that_is_the_fixed_point_921e70_initial the_element_that_is_the_fixed_point_921e70_s109 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l0 the_element_that_is_the_fixed_point_921e70_initial the_element_that_is_the_fixed_point_921e70_s0) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l1 the_element_that_is_the_fixed_point_921e70_s0 the_element_that_is_the_fixed_point_921e70_s1) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l2 the_element_that_is_the_fixed_point_921e70_s1 the_element_that_is_the_fixed_point_921e70_s2) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l3 the_element_that_is_the_fixed_point_921e70_s2 the_element_that_is_the_fixed_point_921e70_s3) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l4 the_element_that_is_the_fixed_point_921e70_s3 the_element_that_is_the_fixed_point_921e70_s4) (.seq (.prod (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l5 the_element_that_is_the_fixed_point_921e70_s4 the_element_that_is_the_fixed_point_921e70_s5) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l6 the_element_that_is_the_fixed_point_921e70_s5 the_element_that_is_the_fixed_point_921e70_s6) (.arrow the_element_that_is_the_fixed_point_921e70_l7 the_element_that_is_the_fixed_point_921e70_s6 the_element_that_is_the_fixed_point_921e70_s7))) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l8 the_element_that_is_the_fixed_point_921e70_s4 the_element_that_is_the_fixed_point_921e70_s8) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l9 the_element_that_is_the_fixed_point_921e70_s8 the_element_that_is_the_fixed_point_921e70_s9) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l10 the_element_that_is_the_fixed_point_921e70_s9 the_element_that_is_the_fixed_point_921e70_s10) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l11 the_element_that_is_the_fixed_point_921e70_s10 the_element_that_is_the_fixed_point_921e70_s11) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l12 the_element_that_is_the_fixed_point_921e70_s11 the_element_that_is_the_fixed_point_921e70_s12) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l13 the_element_that_is_the_fixed_point_921e70_s12 the_element_that_is_the_fixed_point_921e70_s13) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l14 the_element_that_is_the_fixed_point_921e70_s13 the_element_that_is_the_fixed_point_921e70_s14) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l15 the_element_that_is_the_fixed_point_921e70_s14 the_element_that_is_the_fixed_point_921e70_s15) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l16 the_element_that_is_the_fixed_point_921e70_s15 the_element_that_is_the_fixed_point_921e70_s16) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l17 the_element_that_is_the_fixed_point_921e70_s16 the_element_that_is_the_fixed_point_921e70_s17) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l18 the_element_that_is_the_fixed_point_921e70_s17 the_element_that_is_the_fixed_point_921e70_s18) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l19 the_element_that_is_the_fixed_point_921e70_s18 the_element_that_is_the_fixed_point_921e70_s19) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l20 the_element_that_is_the_fixed_point_921e70_s19 the_element_that_is_the_fixed_point_921e70_s20) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l21 the_element_that_is_the_fixed_point_921e70_s20 the_element_that_is_the_fixed_point_921e70_s21) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l22 the_element_that_is_the_fixed_point_921e70_s21 the_element_that_is_the_fixed_point_921e70_s22) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l23 the_element_that_is_the_fixed_point_921e70_s22 the_element_that_is_the_fixed_point_921e70_s23) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l24 the_element_that_is_the_fixed_point_921e70_s23 the_element_that_is_the_fixed_point_921e70_s24) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l25 the_element_that_is_the_fixed_point_921e70_s24 the_element_that_is_the_fixed_point_921e70_s25) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l26 the_element_that_is_the_fixed_point_921e70_s25 the_element_that_is_the_fixed_point_921e70_s26) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l27 the_element_that_is_the_fixed_point_921e70_s26 the_element_that_is_the_fixed_point_921e70_s27) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l28 the_element_that_is_the_fixed_point_921e70_s27 the_element_that_is_the_fixed_point_921e70_s28) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l29 the_element_that_is_the_fixed_point_921e70_s28 the_element_that_is_the_fixed_point_921e70_s29) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l30 the_element_that_is_the_fixed_point_921e70_s29 the_element_that_is_the_fixed_point_921e70_s30) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l31 the_element_that_is_the_fixed_point_921e70_s30 the_element_that_is_the_fixed_point_921e70_s31) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l32 the_element_that_is_the_fixed_point_921e70_s31 the_element_that_is_the_fixed_point_921e70_s32) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l33 the_element_that_is_the_fixed_point_921e70_s32 the_element_that_is_the_fixed_point_921e70_s33) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l34 the_element_that_is_the_fixed_point_921e70_s33 the_element_that_is_the_fixed_point_921e70_s34) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l35 the_element_that_is_the_fixed_point_921e70_s34 the_element_that_is_the_fixed_point_921e70_s35) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l36 the_element_that_is_the_fixed_point_921e70_s35 the_element_that_is_the_fixed_point_921e70_s36) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l37 the_element_that_is_the_fixed_point_921e70_s36 the_element_that_is_the_fixed_point_921e70_s37) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l38 the_element_that_is_the_fixed_point_921e70_s37 the_element_that_is_the_fixed_point_921e70_s38) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l39 the_element_that_is_the_fixed_point_921e70_s38 the_element_that_is_the_fixed_point_921e70_s39) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l40 the_element_that_is_the_fixed_point_921e70_s39 the_element_that_is_the_fixed_point_921e70_s40) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l41 the_element_that_is_the_fixed_point_921e70_s40 the_element_that_is_the_fixed_point_921e70_s41) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l42 the_element_that_is_the_fixed_point_921e70_s41 the_element_that_is_the_fixed_point_921e70_s42) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l43 the_element_that_is_the_fixed_point_921e70_s42 the_element_that_is_the_fixed_point_921e70_s43) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l44 the_element_that_is_the_fixed_point_921e70_s43 the_element_that_is_the_fixed_point_921e70_s44) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l45 the_element_that_is_the_fixed_point_921e70_s44 the_element_that_is_the_fixed_point_921e70_s45) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l46 the_element_that_is_the_fixed_point_921e70_s45 the_element_that_is_the_fixed_point_921e70_s46) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l47 the_element_that_is_the_fixed_point_921e70_s46 the_element_that_is_the_fixed_point_921e70_s47) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l48 the_element_that_is_the_fixed_point_921e70_s47 the_element_that_is_the_fixed_point_921e70_s48) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l49 the_element_that_is_the_fixed_point_921e70_s48 the_element_that_is_the_fixed_point_921e70_s49) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l50 the_element_that_is_the_fixed_point_921e70_s49 the_element_that_is_the_fixed_point_921e70_s50) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l51 the_element_that_is_the_fixed_point_921e70_s50 the_element_that_is_the_fixed_point_921e70_s51) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l52 the_element_that_is_the_fixed_point_921e70_s51 the_element_that_is_the_fixed_point_921e70_s52) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l53 the_element_that_is_the_fixed_point_921e70_s52 the_element_that_is_the_fixed_point_921e70_s53) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l54 the_element_that_is_the_fixed_point_921e70_s53 the_element_that_is_the_fixed_point_921e70_s54) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l55 the_element_that_is_the_fixed_point_921e70_s54 the_element_that_is_the_fixed_point_921e70_s55) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l56 the_element_that_is_the_fixed_point_921e70_s55 the_element_that_is_the_fixed_point_921e70_s56) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l57 the_element_that_is_the_fixed_point_921e70_s56 the_element_that_is_the_fixed_point_921e70_s57) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l58 the_element_that_is_the_fixed_point_921e70_s57 the_element_that_is_the_fixed_point_921e70_s58) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l59 the_element_that_is_the_fixed_point_921e70_s58 the_element_that_is_the_fixed_point_921e70_s59) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l60 the_element_that_is_the_fixed_point_921e70_s59 the_element_that_is_the_fixed_point_921e70_s60) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l61 the_element_that_is_the_fixed_point_921e70_s60 the_element_that_is_the_fixed_point_921e70_s61) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l62 the_element_that_is_the_fixed_point_921e70_s61 the_element_that_is_the_fixed_point_921e70_s62) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l63 the_element_that_is_the_fixed_point_921e70_s62 the_element_that_is_the_fixed_point_921e70_s63) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l64 the_element_that_is_the_fixed_point_921e70_s63 the_element_that_is_the_fixed_point_921e70_s64) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l65 the_element_that_is_the_fixed_point_921e70_s64 the_element_that_is_the_fixed_point_921e70_s65) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l66 the_element_that_is_the_fixed_point_921e70_s65 the_element_that_is_the_fixed_point_921e70_s66) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l67 the_element_that_is_the_fixed_point_921e70_s66 the_element_that_is_the_fixed_point_921e70_s67) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l68 the_element_that_is_the_fixed_point_921e70_s67 the_element_that_is_the_fixed_point_921e70_s68) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l69 the_element_that_is_the_fixed_point_921e70_s68 the_element_that_is_the_fixed_point_921e70_s69) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l70 the_element_that_is_the_fixed_point_921e70_s69 the_element_that_is_the_fixed_point_921e70_s70) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l71 the_element_that_is_the_fixed_point_921e70_s70 the_element_that_is_the_fixed_point_921e70_s71) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l72 the_element_that_is_the_fixed_point_921e70_s71 the_element_that_is_the_fixed_point_921e70_s72) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l73 the_element_that_is_the_fixed_point_921e70_s72 the_element_that_is_the_fixed_point_921e70_s73) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l74 the_element_that_is_the_fixed_point_921e70_s73 the_element_that_is_the_fixed_point_921e70_s74) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l75 the_element_that_is_the_fixed_point_921e70_s74 the_element_that_is_the_fixed_point_921e70_s75) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l76 the_element_that_is_the_fixed_point_921e70_s75 the_element_that_is_the_fixed_point_921e70_s76) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l77 the_element_that_is_the_fixed_point_921e70_s76 the_element_that_is_the_fixed_point_921e70_s77) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l78 the_element_that_is_the_fixed_point_921e70_s77 the_element_that_is_the_fixed_point_921e70_s78) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l79 the_element_that_is_the_fixed_point_921e70_s78 the_element_that_is_the_fixed_point_921e70_s79) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l80 the_element_that_is_the_fixed_point_921e70_s79 the_element_that_is_the_fixed_point_921e70_s80) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l81 the_element_that_is_the_fixed_point_921e70_s80 the_element_that_is_the_fixed_point_921e70_s81) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l82 the_element_that_is_the_fixed_point_921e70_s81 the_element_that_is_the_fixed_point_921e70_s82) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l83 the_element_that_is_the_fixed_point_921e70_s82 the_element_that_is_the_fixed_point_921e70_s83) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l84 the_element_that_is_the_fixed_point_921e70_s83 the_element_that_is_the_fixed_point_921e70_s84) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l85 the_element_that_is_the_fixed_point_921e70_s84 the_element_that_is_the_fixed_point_921e70_s85) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l86 the_element_that_is_the_fixed_point_921e70_s85 the_element_that_is_the_fixed_point_921e70_s86) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l87 the_element_that_is_the_fixed_point_921e70_s86 the_element_that_is_the_fixed_point_921e70_s87) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l88 the_element_that_is_the_fixed_point_921e70_s87 the_element_that_is_the_fixed_point_921e70_s88) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l89 the_element_that_is_the_fixed_point_921e70_s88 the_element_that_is_the_fixed_point_921e70_s89) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l90 the_element_that_is_the_fixed_point_921e70_s89 the_element_that_is_the_fixed_point_921e70_s90) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l91 the_element_that_is_the_fixed_point_921e70_s90 the_element_that_is_the_fixed_point_921e70_s91) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l92 the_element_that_is_the_fixed_point_921e70_s91 the_element_that_is_the_fixed_point_921e70_s92) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l93 the_element_that_is_the_fixed_point_921e70_s92 the_element_that_is_the_fixed_point_921e70_s93) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l94 the_element_that_is_the_fixed_point_921e70_s93 the_element_that_is_the_fixed_point_921e70_s94) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l95 the_element_that_is_the_fixed_point_921e70_s94 the_element_that_is_the_fixed_point_921e70_s95) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l96 the_element_that_is_the_fixed_point_921e70_s95 the_element_that_is_the_fixed_point_921e70_s96) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l97 the_element_that_is_the_fixed_point_921e70_s96 the_element_that_is_the_fixed_point_921e70_s97) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l98 the_element_that_is_the_fixed_point_921e70_s97 the_element_that_is_the_fixed_point_921e70_s98) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l99 the_element_that_is_the_fixed_point_921e70_s98 the_element_that_is_the_fixed_point_921e70_s99) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l100 the_element_that_is_the_fixed_point_921e70_s99 the_element_that_is_the_fixed_point_921e70_s100) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l101 the_element_that_is_the_fixed_point_921e70_s100 the_element_that_is_the_fixed_point_921e70_s101) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l102 the_element_that_is_the_fixed_point_921e70_s101 the_element_that_is_the_fixed_point_921e70_s102) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l103 the_element_that_is_the_fixed_point_921e70_s102 the_element_that_is_the_fixed_point_921e70_s103) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l104 the_element_that_is_the_fixed_point_921e70_s103 the_element_that_is_the_fixed_point_921e70_s104) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l105 the_element_that_is_the_fixed_point_921e70_s104 the_element_that_is_the_fixed_point_921e70_s105) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l106 the_element_that_is_the_fixed_point_921e70_s105 the_element_that_is_the_fixed_point_921e70_s106) (.arrow the_element_that_is_the_fixed_point_921e70_l107 the_element_that_is_the_fixed_point_921e70_s106 the_element_that_is_the_fixed_point_921e70_s107))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow the_element_that_is_the_fixed_point_921e70_l108 (tensorProduct the_element_that_is_the_fixed_point_921e70_s7 the_element_that_is_the_fixed_point_921e70_s107) the_element_that_is_the_fixed_point_921e70_s108) (.arrow the_element_that_is_the_fixed_point_921e70_l109 the_element_that_is_the_fixed_point_921e70_s108 the_element_that_is_the_fixed_point_921e70_s109))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_element_that_is_the_fixed_point_921e70_true_arm : IGProtocol the_element_that_is_the_fixed_point_921e70_initial the_element_that_is_the_fixed_point_921e70_s109 :=
  (the_element_that_is_the_fixed_point_921e70_protocol).restrictToEVALT

-- false arm
noncomputable def the_element_that_is_the_fixed_point_921e70_false_arm : IGProtocol the_element_that_is_the_fixed_point_921e70_initial the_element_that_is_the_fixed_point_921e70_s109 :=
  (the_element_that_is_the_fixed_point_921e70_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_element_that_is_the_fixed_point_921e70_tier_ground : OuroboricityTier := TierFunctor.obj the_element_that_is_the_fixed_point_921e70_initial
def the_element_that_is_the_fixed_point_921e70_tier : OuroboricityTier := TierFunctor.obj the_element_that_is_the_fixed_point_921e70_s109
#eval the_element_that_is_the_fixed_point_921e70_tier_ground  -- tier of the ground (pre-transformation)
#eval the_element_that_is_the_fixed_point_921e70_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem the_element_that_is_the_fixed_point_921e70_frobenius :
    igFrobeniusAlg.mul the_element_that_is_the_fixed_point_921e70_initial the_element_that_is_the_fixed_point_921e70_initial = the_element_that_is_the_fixed_point_921e70_initial :=
  igFrobAlg_self_fusion the_element_that_is_the_fixed_point_921e70_initial

theorem the_element_that_is_the_fixed_point_921e70_protocol_depth :
    the_element_that_is_the_fixed_point_921e70_protocol.depth = 107 := by rfl

end Imscribing