-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊡ → ≺ → ⊥ → ∋ → ⊙ → ⊣ → ⊢ → ⊙ → ≻ → ⊡ → ∈ → ⊤ → ⋈ → ≺ → ∋ → ⊞ → ⊣ → ⊢ → ⊙ → ∈ → ≻ → ⊤ → ≺ → ⊥ → ∋ → ⋈ → ⊞ → ⊡ → ⊣ → ⊢ → ∈ → ⊤ → ≻ → ≺ → ⋈ → ⊙ → ∋ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ∋ → ≺ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⊡ → ⊥ → ≺ → ∋ → ⋈ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⊥ → ∋ → ⋈ → ⊙ → ⊡ → ⊣ → ⊢ → ⊙ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊥ → ⊡ → ∋ → ⊞ → ⊣ → ⊢ → ≻ → ∈ → ⊤ → ⊙ → ∋ → ⋈ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊡ → ≺ → ⊥ → ∋ → ⊞ → ⊙ → ⊡ → ⊣ → ⊢ → ⊙ → ∈ → ⊤ → ≻ → ≺ → ∋ → ∈ → ⊥ → ∋ → ⋈ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ∋ → ⊙ → ⊡ → ⊣
-- Class: eternal_existence
-- Fingerprint: sig=(73,26,26,15)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=140
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 9), (16, 20), (25, 30), (36, 42), (49, 52), (60, 65), (73, 76), (84, 91), (96, 99), (106, 112), (119, 123), (124, 126), (133, 136)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [4] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [12] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [13] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [14] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [15] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [16] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [17] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [18] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [19] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [20] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [21] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [22] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [23] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [24] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [25] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [26] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [27] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [28] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [29] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [30] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [31] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [32] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [33] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [34] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [35] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [36] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [37] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [38] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [39] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [40] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [41] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [42] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [43] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [44] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [45] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [46] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [47] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [50] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [51] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [52] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [53] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [54] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [55] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [56] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [57] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [58] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [59] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [60] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [61] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [62] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [63] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [64] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [65] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [66] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [67] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [68] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [69] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [70] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [71] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [72] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [73] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [74] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [75] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [76] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [77] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [78] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [79] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [80] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [81] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [82] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [83] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [84] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [85] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [86] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [87] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [88] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [89] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [90] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [91] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [92] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [93] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [94] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [95] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [96] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [97] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [98] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [99] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [100] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [101] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [102] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [103] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [104] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [105] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [106] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [107] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [108] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [109] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [110] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [111] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [112] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [113] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [114] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [115] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [116] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [117] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [118] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [119] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [120] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [121] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [122] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [123] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [124] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [125] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [126] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [127] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [128] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [129] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [130] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [131] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [132] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [133] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [134] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [135] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [136] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [137] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [138] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [139] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def eternal_existence_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s100 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s101 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s102 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s103 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s104 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s105 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s106 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s107 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s108 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s109 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s110 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s111 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s112 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s113 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s114 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s115 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s116 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s117 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s118 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s119 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s120 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s121 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s122 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def eternal_existence_s123 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s124 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s125 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s126 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s127 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s128 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s129 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s130 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s131 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s132 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s133 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s134 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s135 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s136 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s137 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s138 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def eternal_existence_s139 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def eternal_existence_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l23 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l26 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l35 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l38 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l46 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l57 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l59 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l70 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l72 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l81 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l82 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l84 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l86 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l91 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l93 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l94 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l95 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l96 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l98 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l100 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l101 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l102 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l103 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l104 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l105 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l106 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l107 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l108 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l109 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l110 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l111 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l112 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l113 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def eternal_existence_l114 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l115 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l116 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l117 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l118 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l119 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l120 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l121 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l122 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l123 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l124 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l125 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def eternal_existence_l126 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l127 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l128 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l129 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l130 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l131 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l132 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l133 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l134 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l135 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l136 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l137 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def eternal_existence_l138 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def eternal_existence_l139 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def eternal_existence_protocol : IGProtocol eternal_existence_initial eternal_existence_s139 :=
  .withGram Grammar.measure <|
  (.seq (.arrow eternal_existence_l0 eternal_existence_initial eternal_existence_s0) (.seq (.arrow eternal_existence_l1 eternal_existence_s0 eternal_existence_s1) (.seq (.arrow eternal_existence_l2 eternal_existence_s1 eternal_existence_s2) (.seq (.prod (.seq (.arrow eternal_existence_l3 eternal_existence_s2 eternal_existence_s3) (.seq (.arrow eternal_existence_l4 eternal_existence_s3 eternal_existence_s4) (.seq (.arrow eternal_existence_l5 eternal_existence_s4 eternal_existence_s5) (.seq (.arrow eternal_existence_l6 eternal_existence_s5 eternal_existence_s6) (.arrow eternal_existence_l7 eternal_existence_s6 eternal_existence_s7))))) (.arrow eternal_existence_l8 eternal_existence_s2 eternal_existence_s8)) (.seq (.arrow eternal_existence_l9 (tensorProduct eternal_existence_s7 eternal_existence_s8) eternal_existence_s9) (.seq (.arrow eternal_existence_l10 eternal_existence_s9 eternal_existence_s10) (.seq (.arrow eternal_existence_l11 eternal_existence_s10 eternal_existence_s11) (.seq (.arrow eternal_existence_l12 eternal_existence_s11 eternal_existence_s12) (.seq (.arrow eternal_existence_l13 eternal_existence_s12 eternal_existence_s13) (.seq (.arrow eternal_existence_l14 eternal_existence_s13 eternal_existence_s14) (.seq (.arrow eternal_existence_l15 eternal_existence_s14 eternal_existence_s15) (.seq (.arrow eternal_existence_l16 eternal_existence_s15 eternal_existence_s16) (.seq (.prod (.seq (.arrow eternal_existence_l17 eternal_existence_s16 eternal_existence_s17) (.arrow eternal_existence_l18 eternal_existence_s17 eternal_existence_s18)) (.arrow eternal_existence_l19 eternal_existence_s16 eternal_existence_s19)) (.seq (.arrow eternal_existence_l20 (tensorProduct eternal_existence_s18 eternal_existence_s19) eternal_existence_s20) (.seq (.arrow eternal_existence_l21 eternal_existence_s20 eternal_existence_s21) (.seq (.arrow eternal_existence_l22 eternal_existence_s21 eternal_existence_s22) (.seq (.arrow eternal_existence_l23 eternal_existence_s22 eternal_existence_s23) (.seq (.arrow eternal_existence_l24 eternal_existence_s23 eternal_existence_s24) (.seq (.arrow eternal_existence_l25 eternal_existence_s24 eternal_existence_s25) (.seq (.prod (.seq (.arrow eternal_existence_l26 eternal_existence_s25 eternal_existence_s26) (.seq (.arrow eternal_existence_l27 eternal_existence_s26 eternal_existence_s27) (.arrow eternal_existence_l28 eternal_existence_s27 eternal_existence_s28))) (.arrow eternal_existence_l29 eternal_existence_s25 eternal_existence_s29)) (.seq (.arrow eternal_existence_l30 (tensorProduct eternal_existence_s28 eternal_existence_s29) eternal_existence_s30) (.seq (.arrow eternal_existence_l31 eternal_existence_s30 eternal_existence_s31) (.seq (.arrow eternal_existence_l32 eternal_existence_s31 eternal_existence_s32) (.seq (.arrow eternal_existence_l33 eternal_existence_s32 eternal_existence_s33) (.seq (.arrow eternal_existence_l34 eternal_existence_s33 eternal_existence_s34) (.seq (.arrow eternal_existence_l35 eternal_existence_s34 eternal_existence_s35) (.seq (.arrow eternal_existence_l36 eternal_existence_s35 eternal_existence_s36) (.seq (.prod (.seq (.arrow eternal_existence_l37 eternal_existence_s36 eternal_existence_s37) (.arrow eternal_existence_l38 eternal_existence_s37 eternal_existence_s38)) (.seq (.arrow eternal_existence_l39 eternal_existence_s36 eternal_existence_s39) (.seq (.arrow eternal_existence_l40 eternal_existence_s39 eternal_existence_s40) (.arrow eternal_existence_l41 eternal_existence_s40 eternal_existence_s41)))) (.seq (.arrow eternal_existence_l42 (tensorProduct eternal_existence_s38 eternal_existence_s41) eternal_existence_s42) (.seq (.arrow eternal_existence_l43 eternal_existence_s42 eternal_existence_s43) (.seq (.arrow eternal_existence_l44 eternal_existence_s43 eternal_existence_s44) (.seq (.arrow eternal_existence_l45 eternal_existence_s44 eternal_existence_s45) (.seq (.arrow eternal_existence_l46 eternal_existence_s45 eternal_existence_s46) (.seq (.arrow eternal_existence_l47 eternal_existence_s46 eternal_existence_s47) (.seq (.arrow eternal_existence_l48 eternal_existence_s47 eternal_existence_s48) (.seq (.arrow eternal_existence_l49 eternal_existence_s48 eternal_existence_s49) (.seq (.prod (.seq (.arrow eternal_existence_l50 eternal_existence_s49 eternal_existence_s50) (.arrow eternal_existence_l51 eternal_existence_s50 eternal_existence_s51)) (.refl eternal_existence_s49)) (.seq (.arrow eternal_existence_l52 (tensorProduct eternal_existence_s51 eternal_existence_s49) eternal_existence_s52) (.seq (.arrow eternal_existence_l53 eternal_existence_s52 eternal_existence_s53) (.seq (.arrow eternal_existence_l54 eternal_existence_s53 eternal_existence_s54) (.seq (.arrow eternal_existence_l55 eternal_existence_s54 eternal_existence_s55) (.seq (.arrow eternal_existence_l56 eternal_existence_s55 eternal_existence_s56) (.seq (.arrow eternal_existence_l57 eternal_existence_s56 eternal_existence_s57) (.seq (.arrow eternal_existence_l58 eternal_existence_s57 eternal_existence_s58) (.seq (.arrow eternal_existence_l59 eternal_existence_s58 eternal_existence_s59) (.seq (.arrow eternal_existence_l60 eternal_existence_s59 eternal_existence_s60) (.seq (.prod (.seq (.arrow eternal_existence_l61 eternal_existence_s60 eternal_existence_s61) (.arrow eternal_existence_l62 eternal_existence_s61 eternal_existence_s62)) (.seq (.arrow eternal_existence_l63 eternal_existence_s60 eternal_existence_s63) (.arrow eternal_existence_l64 eternal_existence_s63 eternal_existence_s64))) (.seq (.arrow eternal_existence_l65 (tensorProduct eternal_existence_s62 eternal_existence_s64) eternal_existence_s65) (.seq (.arrow eternal_existence_l66 eternal_existence_s65 eternal_existence_s66) (.seq (.arrow eternal_existence_l67 eternal_existence_s66 eternal_existence_s67) (.seq (.arrow eternal_existence_l68 eternal_existence_s67 eternal_existence_s68) (.seq (.arrow eternal_existence_l69 eternal_existence_s68 eternal_existence_s69) (.seq (.arrow eternal_existence_l70 eternal_existence_s69 eternal_existence_s70) (.seq (.arrow eternal_existence_l71 eternal_existence_s70 eternal_existence_s71) (.seq (.arrow eternal_existence_l72 eternal_existence_s71 eternal_existence_s72) (.seq (.arrow eternal_existence_l73 eternal_existence_s72 eternal_existence_s73) (.seq (.prod (.arrow eternal_existence_l74 eternal_existence_s73 eternal_existence_s74) (.arrow eternal_existence_l75 eternal_existence_s73 eternal_existence_s75)) (.seq (.arrow eternal_existence_l76 (tensorProduct eternal_existence_s74 eternal_existence_s75) eternal_existence_s76) (.seq (.arrow eternal_existence_l77 eternal_existence_s76 eternal_existence_s77) (.seq (.arrow eternal_existence_l78 eternal_existence_s77 eternal_existence_s78) (.seq (.arrow eternal_existence_l79 eternal_existence_s78 eternal_existence_s79) (.seq (.arrow eternal_existence_l80 eternal_existence_s79 eternal_existence_s80) (.seq (.arrow eternal_existence_l81 eternal_existence_s80 eternal_existence_s81) (.seq (.arrow eternal_existence_l82 eternal_existence_s81 eternal_existence_s82) (.seq (.arrow eternal_existence_l83 eternal_existence_s82 eternal_existence_s83) (.seq (.arrow eternal_existence_l84 eternal_existence_s83 eternal_existence_s84) (.seq (.prod (.seq (.arrow eternal_existence_l85 eternal_existence_s84 eternal_existence_s85) (.seq (.arrow eternal_existence_l86 eternal_existence_s85 eternal_existence_s86) (.seq (.arrow eternal_existence_l87 eternal_existence_s86 eternal_existence_s87) (.arrow eternal_existence_l88 eternal_existence_s87 eternal_existence_s88)))) (.seq (.arrow eternal_existence_l89 eternal_existence_s84 eternal_existence_s89) (.arrow eternal_existence_l90 eternal_existence_s89 eternal_existence_s90))) (.seq (.arrow eternal_existence_l91 (tensorProduct eternal_existence_s88 eternal_existence_s90) eternal_existence_s91) (.seq (.arrow eternal_existence_l92 eternal_existence_s91 eternal_existence_s92) (.seq (.arrow eternal_existence_l93 eternal_existence_s92 eternal_existence_s93) (.seq (.arrow eternal_existence_l94 eternal_existence_s93 eternal_existence_s94) (.seq (.arrow eternal_existence_l95 eternal_existence_s94 eternal_existence_s95) (.seq (.arrow eternal_existence_l96 eternal_existence_s95 eternal_existence_s96) (.seq (.prod (.seq (.arrow eternal_existence_l97 eternal_existence_s96 eternal_existence_s97) (.arrow eternal_existence_l98 eternal_existence_s97 eternal_existence_s98)) (.refl eternal_existence_s96)) (.seq (.arrow eternal_existence_l99 (tensorProduct eternal_existence_s98 eternal_existence_s96) eternal_existence_s99) (.seq (.arrow eternal_existence_l100 eternal_existence_s99 eternal_existence_s100) (.seq (.arrow eternal_existence_l101 eternal_existence_s100 eternal_existence_s101) (.seq (.arrow eternal_existence_l102 eternal_existence_s101 eternal_existence_s102) (.seq (.arrow eternal_existence_l103 eternal_existence_s102 eternal_existence_s103) (.seq (.arrow eternal_existence_l104 eternal_existence_s103 eternal_existence_s104) (.seq (.arrow eternal_existence_l105 eternal_existence_s104 eternal_existence_s105) (.seq (.arrow eternal_existence_l106 eternal_existence_s105 eternal_existence_s106) (.seq (.prod (.seq (.arrow eternal_existence_l107 eternal_existence_s106 eternal_existence_s107) (.seq (.arrow eternal_existence_l108 eternal_existence_s107 eternal_existence_s108) (.seq (.arrow eternal_existence_l109 eternal_existence_s108 eternal_existence_s109) (.arrow eternal_existence_l110 eternal_existence_s109 eternal_existence_s110)))) (.arrow eternal_existence_l111 eternal_existence_s106 eternal_existence_s111)) (.seq (.arrow eternal_existence_l112 (tensorProduct eternal_existence_s110 eternal_existence_s111) eternal_existence_s112) (.seq (.arrow eternal_existence_l113 eternal_existence_s112 eternal_existence_s113) (.seq (.arrow eternal_existence_l114 eternal_existence_s113 eternal_existence_s114) (.seq (.arrow eternal_existence_l115 eternal_existence_s114 eternal_existence_s115) (.seq (.arrow eternal_existence_l116 eternal_existence_s115 eternal_existence_s116) (.seq (.arrow eternal_existence_l117 eternal_existence_s116 eternal_existence_s117) (.seq (.arrow eternal_existence_l118 eternal_existence_s117 eternal_existence_s118) (.seq (.arrow eternal_existence_l119 eternal_existence_s118 eternal_existence_s119) (.seq (.prod (.seq (.arrow eternal_existence_l120 eternal_existence_s119 eternal_existence_s120) (.arrow eternal_existence_l121 eternal_existence_s120 eternal_existence_s121)) (.arrow eternal_existence_l122 eternal_existence_s119 eternal_existence_s122)) (.seq (.arrow eternal_existence_l123 (tensorProduct eternal_existence_s121 eternal_existence_s122) eternal_existence_s123) (.seq (.arrow eternal_existence_l124 eternal_existence_s123 eternal_existence_s124) (.seq (.prod (.refl eternal_existence_s124) (.arrow eternal_existence_l125 eternal_existence_s124 eternal_existence_s125)) (.seq (.arrow eternal_existence_l126 (tensorProduct eternal_existence_s124 eternal_existence_s125) eternal_existence_s126) (.seq (.arrow eternal_existence_l127 eternal_existence_s126 eternal_existence_s127) (.seq (.arrow eternal_existence_l128 eternal_existence_s127 eternal_existence_s128) (.seq (.arrow eternal_existence_l129 eternal_existence_s128 eternal_existence_s129) (.seq (.arrow eternal_existence_l130 eternal_existence_s129 eternal_existence_s130) (.seq (.arrow eternal_existence_l131 eternal_existence_s130 eternal_existence_s131) (.seq (.arrow eternal_existence_l132 eternal_existence_s131 eternal_existence_s132) (.seq (.arrow eternal_existence_l133 eternal_existence_s132 eternal_existence_s133) (.seq (.prod (.seq (.arrow eternal_existence_l134 eternal_existence_s133 eternal_existence_s134) (.arrow eternal_existence_l135 eternal_existence_s134 eternal_existence_s135)) (.refl eternal_existence_s133)) (.seq (.arrow eternal_existence_l136 (tensorProduct eternal_existence_s135 eternal_existence_s133) eternal_existence_s136) (.seq (.arrow eternal_existence_l137 eternal_existence_s136 eternal_existence_s137) (.seq (.arrow eternal_existence_l138 eternal_existence_s137 eternal_existence_s138) (.arrow eternal_existence_l139 eternal_existence_s138 eternal_existence_s139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def eternal_existence_true_arm : IGProtocol eternal_existence_initial eternal_existence_s139 :=
  (eternal_existence_protocol).restrictToEVALT

-- false arm
noncomputable def eternal_existence_false_arm : IGProtocol eternal_existence_initial eternal_existence_s139 :=
  (eternal_existence_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def eternal_existence_tier_ground : OuroboricityTier := TierFunctor.obj eternal_existence_initial
def eternal_existence_tier : OuroboricityTier := TierFunctor.obj eternal_existence_s139
#eval eternal_existence_tier_ground  -- tier of the ground (pre-transformation)
#eval eternal_existence_tier  -- the Grammar's tuple-tier verdict

theorem eternal_existence_protocol_depth :
    eternal_existence_protocol.depth = 128 := by rfl

end Imscribing