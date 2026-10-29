-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≺ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊙ → ≻ → ⊤ → ⋈ → ⊡ → ⊥ → ≺ → ⊞ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⊞ → ⊡ → ⊙ → ⋈ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ⊤ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊤ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊤ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊤ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊡ → ∋ → ⊣
-- Class: snow
-- Fingerprint: sig=(51,2,29,18)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=100
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 98)]

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
--   [6] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [13] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [14] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [15] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [16] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [17] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [18] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [19] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [20] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [21] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [24] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [27] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [28] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [29] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [30] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [31] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [32] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [33] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [34] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [35] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [36] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [37] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [38] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [39] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [40] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [41] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [42] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [43] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [44] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [45] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [46] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [47] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [48] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [49] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [50] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [51] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [52] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [53] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [55] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [56] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [57] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [58] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [59] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [60] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [61] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [62] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [63] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [64] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [65] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [66] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [67] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [68] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [69] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [70] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [71] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [72] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [73] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [74] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [75] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [76] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [77] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [78] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [79] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [80] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [81] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [82] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [83] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [84] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [85] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [86] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [87] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [88] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [89] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [90] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [91] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [92] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [93] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [94] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [95] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [96] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [97] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [98] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [99] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def snow_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def snow_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def snow_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def snow_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def snow_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def snow_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def snow_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def snow_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l16 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def snow_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l32 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def snow_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def snow_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l81 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l82 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l84 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l91 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def snow_l93 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l94 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def snow_l95 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l96 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def snow_l98 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def snow_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def snow_protocol : IGProtocol snow_initial snow_s99 :=
  .withGram Grammar.measure <|
  (.seq (.arrow snow_l0 snow_initial snow_s0) (.seq (.arrow snow_l1 snow_s0 snow_s1) (.seq (.arrow snow_l2 snow_s1 snow_s2) (.seq (.arrow snow_l3 snow_s2 snow_s3) (.seq (.arrow snow_l4 snow_s3 snow_s4) (.seq (.prod (.seq (.arrow snow_l5 snow_s4 snow_s5) (.seq (.arrow snow_l6 snow_s5 snow_s6) (.seq (.arrow snow_l7 snow_s6 snow_s7) (.seq (.arrow snow_l8 snow_s7 snow_s8) (.seq (.arrow snow_l9 snow_s8 snow_s9) (.seq (.arrow snow_l10 snow_s9 snow_s10) (.seq (.arrow snow_l11 snow_s10 snow_s11) (.seq (.arrow snow_l12 snow_s11 snow_s12) (.seq (.arrow snow_l13 snow_s12 snow_s13) (.seq (.arrow snow_l14 snow_s13 snow_s14) (.seq (.arrow snow_l15 snow_s14 snow_s15) (.seq (.arrow snow_l16 snow_s15 snow_s16) (.seq (.arrow snow_l17 snow_s16 snow_s17) (.seq (.arrow snow_l18 snow_s17 snow_s18) (.seq (.arrow snow_l19 snow_s18 snow_s19) (.seq (.arrow snow_l20 snow_s19 snow_s20) (.seq (.arrow snow_l21 snow_s20 snow_s21) (.seq (.arrow snow_l22 snow_s21 snow_s22) (.seq (.arrow snow_l23 snow_s22 snow_s23) (.seq (.arrow snow_l24 snow_s23 snow_s24) (.arrow snow_l25 snow_s24 snow_s25))))))))))))))))))))) (.seq (.arrow snow_l26 snow_s4 snow_s26) (.seq (.arrow snow_l27 snow_s26 snow_s27) (.seq (.arrow snow_l28 snow_s27 snow_s28) (.seq (.arrow snow_l29 snow_s28 snow_s29) (.seq (.arrow snow_l30 snow_s29 snow_s30) (.seq (.arrow snow_l31 snow_s30 snow_s31) (.seq (.arrow snow_l32 snow_s31 snow_s32) (.seq (.arrow snow_l33 snow_s32 snow_s33) (.seq (.arrow snow_l34 snow_s33 snow_s34) (.seq (.arrow snow_l35 snow_s34 snow_s35) (.seq (.arrow snow_l36 snow_s35 snow_s36) (.seq (.arrow snow_l37 snow_s36 snow_s37) (.seq (.arrow snow_l38 snow_s37 snow_s38) (.seq (.arrow snow_l39 snow_s38 snow_s39) (.seq (.arrow snow_l40 snow_s39 snow_s40) (.seq (.arrow snow_l41 snow_s40 snow_s41) (.seq (.arrow snow_l42 snow_s41 snow_s42) (.seq (.arrow snow_l43 snow_s42 snow_s43) (.seq (.arrow snow_l44 snow_s43 snow_s44) (.seq (.arrow snow_l45 snow_s44 snow_s45) (.seq (.arrow snow_l46 snow_s45 snow_s46) (.seq (.arrow snow_l47 snow_s46 snow_s47) (.seq (.arrow snow_l48 snow_s47 snow_s48) (.seq (.arrow snow_l49 snow_s48 snow_s49) (.seq (.arrow snow_l50 snow_s49 snow_s50) (.seq (.arrow snow_l51 snow_s50 snow_s51) (.seq (.arrow snow_l52 snow_s51 snow_s52) (.seq (.arrow snow_l53 snow_s52 snow_s53) (.seq (.arrow snow_l54 snow_s53 snow_s54) (.seq (.arrow snow_l55 snow_s54 snow_s55) (.seq (.arrow snow_l56 snow_s55 snow_s56) (.seq (.arrow snow_l57 snow_s56 snow_s57) (.seq (.arrow snow_l58 snow_s57 snow_s58) (.seq (.arrow snow_l59 snow_s58 snow_s59) (.seq (.arrow snow_l60 snow_s59 snow_s60) (.seq (.arrow snow_l61 snow_s60 snow_s61) (.seq (.arrow snow_l62 snow_s61 snow_s62) (.seq (.arrow snow_l63 snow_s62 snow_s63) (.seq (.arrow snow_l64 snow_s63 snow_s64) (.seq (.arrow snow_l65 snow_s64 snow_s65) (.seq (.arrow snow_l66 snow_s65 snow_s66) (.seq (.arrow snow_l67 snow_s66 snow_s67) (.seq (.arrow snow_l68 snow_s67 snow_s68) (.seq (.arrow snow_l69 snow_s68 snow_s69) (.seq (.arrow snow_l70 snow_s69 snow_s70) (.seq (.arrow snow_l71 snow_s70 snow_s71) (.seq (.arrow snow_l72 snow_s71 snow_s72) (.seq (.arrow snow_l73 snow_s72 snow_s73) (.seq (.arrow snow_l74 snow_s73 snow_s74) (.seq (.arrow snow_l75 snow_s74 snow_s75) (.seq (.arrow snow_l76 snow_s75 snow_s76) (.seq (.arrow snow_l77 snow_s76 snow_s77) (.seq (.arrow snow_l78 snow_s77 snow_s78) (.seq (.arrow snow_l79 snow_s78 snow_s79) (.seq (.arrow snow_l80 snow_s79 snow_s80) (.seq (.arrow snow_l81 snow_s80 snow_s81) (.seq (.arrow snow_l82 snow_s81 snow_s82) (.seq (.arrow snow_l83 snow_s82 snow_s83) (.seq (.arrow snow_l84 snow_s83 snow_s84) (.seq (.arrow snow_l85 snow_s84 snow_s85) (.seq (.arrow snow_l86 snow_s85 snow_s86) (.seq (.arrow snow_l87 snow_s86 snow_s87) (.seq (.arrow snow_l88 snow_s87 snow_s88) (.seq (.arrow snow_l89 snow_s88 snow_s89) (.seq (.arrow snow_l90 snow_s89 snow_s90) (.seq (.arrow snow_l91 snow_s90 snow_s91) (.seq (.arrow snow_l92 snow_s91 snow_s92) (.seq (.arrow snow_l93 snow_s92 snow_s93) (.seq (.arrow snow_l94 snow_s93 snow_s94) (.seq (.arrow snow_l95 snow_s94 snow_s95) (.seq (.arrow snow_l96 snow_s95 snow_s96) (.arrow snow_l97 snow_s96 snow_s97))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow snow_l98 (tensorProduct snow_s25 snow_s97) snow_s98) (.arrow snow_l99 snow_s98 snow_s99))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def snow_true_arm : IGProtocol snow_initial snow_s99 :=
  (snow_protocol).restrictToEVALT

-- false arm
noncomputable def snow_false_arm : IGProtocol snow_initial snow_s99 :=
  (snow_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def snow_tier_ground : OuroboricityTier := TierFunctor.obj snow_initial
def snow_tier : OuroboricityTier := TierFunctor.obj snow_s99
#eval snow_tier_ground  -- tier of the ground (pre-transformation)
#eval snow_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem snow_frobenius :
    igFrobeniusAlg.mul snow_initial snow_initial = snow_initial :=
  igFrobAlg_self_fusion snow_initial

theorem snow_protocol_depth :
    snow_protocol.depth = 79 := by rfl

end Imscribing