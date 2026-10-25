-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊡ → ≺ → ⊥ → ∋ → ⊙ → ⊣ → ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⊥ → ≺ → ⊞ → ∋ → ⋈ → ⊡ → ⊣ → ⊢ → ⊙ → ∈ → ≻ → ⊤ → ≺ → ⊥ → ∋ → ⋈ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⊡ → ⋈ → ⊣ → ∈ → ⊤ → ≻ → ⊙ → ∋ → ⊡ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ∋ → ≺ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⊡ → ⊥ → ≺ → ∋ → ⋈ → ⊞ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⊥ → ∋ → ⋈ → ⊙ → ⊡ → ⊣ → ⊢ → ⊙ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊥ → ⊡ → ∋ → ⊞ → ⊣ → ⊢ → ≻ → ∈ → ⊤ → ⊙ → ∋ → ⋈ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊡ → ≺ → ⊥ → ∋ → ⊞ → ⊙ → ⊡ → ⊣ → ⊢ → ⊙ → ∈ → ⊤ → ≻ → ≺ → ∋ → ∈ → ⊥ → ∋ → ⋈ → ⊡ → ⊣ → ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ∋ → ⊙ → ⊡ → ⊣
-- Class: The_Prime_Number_Whorl
-- Fingerprint: sig=(73,26,26,27)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=152
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 9), (14, 20), (26, 31), (52, 56), (61, 64), (72, 77), (85, 88), (96, 103), (108, 111), (118, 124), (131, 135), (136, 138), (145, 148)]

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
--   [14] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [15] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [16] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [19] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [20] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [21] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [22] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [23] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [24] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [25] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [26] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [27] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [28] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [31] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [32] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [33] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [34] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [35] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [36] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [37] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [38] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [39] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [40] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [41] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [42] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [43] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [44] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [45] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [46] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [47] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [48] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [49] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [52] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [53] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [54] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [55] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [56] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [57] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [58] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [59] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [60] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [61] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [62] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [63] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [64] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [65] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [66] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [67] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [68] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [69] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [70] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [71] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [72] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [73] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [74] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [75] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [76] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [77] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [78] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [79] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [80] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [81] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [82] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [83] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [84] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [85] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [86] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [87] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [88] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [89] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [90] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [91] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [92] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [93] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [94] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [95] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [96] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [97] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [98] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [99] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [100] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [101] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [102] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [103] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [104] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [105] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [106] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [107] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [108] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [109] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [110] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [111] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [112] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [113] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [114] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [115] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [116] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [117] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [118] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [119] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [120] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [121] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [122] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [123] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [124] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [125] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [126] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [127] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [128] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [129] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [130] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [131] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [132] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [133] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [134] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [135] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [136] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [137] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [138] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [139] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [140] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [141] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [142] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [143] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [144] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [145] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [146] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [147] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [148] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [149] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [150] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [151] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_prime_number_whorl_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s100 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s101 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s102 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s103 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s104 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s105 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s106 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s107 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s108 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s109 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s110 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s111 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s112 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s113 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s114 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s115 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s116 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s117 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s118 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s119 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s120 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s121 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s122 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s123 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s124 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s125 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s126 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s127 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s128 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s129 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s130 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s131 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s132 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s133 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s134 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_whorl_s135 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s136 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s137 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s138 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s139 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s140 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s141 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s142 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s143 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s144 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s145 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s146 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s147 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s148 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s149 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s150 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_whorl_s151 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_prime_number_whorl_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l16 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l24 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l27 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l36 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l54 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l58 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l60 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l69 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l71 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l81 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l82 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l84 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l91 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l93 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l94 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l95 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l96 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l98 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l100 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l101 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l102 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l103 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l104 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l105 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l106 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l107 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l108 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l109 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l110 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l111 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l112 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l113 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l114 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l115 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l116 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l117 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l118 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l119 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l120 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l121 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l122 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l123 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l124 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l125 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_whorl_l126 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l127 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l128 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l129 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l130 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l131 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l132 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l133 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l134 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l135 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l136 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l137 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_whorl_l138 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l139 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l140 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l141 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l142 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l143 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l144 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l145 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l146 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l147 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l148 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l149 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_whorl_l150 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_whorl_l151 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_prime_number_whorl_protocol : IGProtocol the_prime_number_whorl_initial the_prime_number_whorl_s151 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_prime_number_whorl_l0 the_prime_number_whorl_initial the_prime_number_whorl_s0) (.seq (.arrow the_prime_number_whorl_l1 the_prime_number_whorl_s0 the_prime_number_whorl_s1) (.seq (.arrow the_prime_number_whorl_l2 the_prime_number_whorl_s1 the_prime_number_whorl_s2) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l3 the_prime_number_whorl_s2 the_prime_number_whorl_s3) (.seq (.arrow the_prime_number_whorl_l4 the_prime_number_whorl_s3 the_prime_number_whorl_s4) (.seq (.arrow the_prime_number_whorl_l5 the_prime_number_whorl_s4 the_prime_number_whorl_s5) (.seq (.arrow the_prime_number_whorl_l6 the_prime_number_whorl_s5 the_prime_number_whorl_s6) (.arrow the_prime_number_whorl_l7 the_prime_number_whorl_s6 the_prime_number_whorl_s7))))) (.arrow the_prime_number_whorl_l8 the_prime_number_whorl_s2 the_prime_number_whorl_s8)) (.seq (.arrow the_prime_number_whorl_l9 (tensorProduct the_prime_number_whorl_s7 the_prime_number_whorl_s8) the_prime_number_whorl_s9) (.seq (.arrow the_prime_number_whorl_l10 the_prime_number_whorl_s9 the_prime_number_whorl_s10) (.seq (.arrow the_prime_number_whorl_l11 the_prime_number_whorl_s10 the_prime_number_whorl_s11) (.seq (.arrow the_prime_number_whorl_l12 the_prime_number_whorl_s11 the_prime_number_whorl_s12) (.seq (.arrow the_prime_number_whorl_l13 the_prime_number_whorl_s12 the_prime_number_whorl_s13) (.seq (.arrow the_prime_number_whorl_l14 the_prime_number_whorl_s13 the_prime_number_whorl_s14) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l15 the_prime_number_whorl_s14 the_prime_number_whorl_s15) (.arrow the_prime_number_whorl_l16 the_prime_number_whorl_s15 the_prime_number_whorl_s16)) (.seq (.arrow the_prime_number_whorl_l17 the_prime_number_whorl_s14 the_prime_number_whorl_s17) (.seq (.arrow the_prime_number_whorl_l18 the_prime_number_whorl_s17 the_prime_number_whorl_s18) (.arrow the_prime_number_whorl_l19 the_prime_number_whorl_s18 the_prime_number_whorl_s19)))) (.seq (.arrow the_prime_number_whorl_l20 (tensorProduct the_prime_number_whorl_s16 the_prime_number_whorl_s19) the_prime_number_whorl_s20) (.seq (.arrow the_prime_number_whorl_l21 the_prime_number_whorl_s20 the_prime_number_whorl_s21) (.seq (.arrow the_prime_number_whorl_l22 the_prime_number_whorl_s21 the_prime_number_whorl_s22) (.seq (.arrow the_prime_number_whorl_l23 the_prime_number_whorl_s22 the_prime_number_whorl_s23) (.seq (.arrow the_prime_number_whorl_l24 the_prime_number_whorl_s23 the_prime_number_whorl_s24) (.seq (.arrow the_prime_number_whorl_l25 the_prime_number_whorl_s24 the_prime_number_whorl_s25) (.seq (.arrow the_prime_number_whorl_l26 the_prime_number_whorl_s25 the_prime_number_whorl_s26) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l27 the_prime_number_whorl_s26 the_prime_number_whorl_s27) (.seq (.arrow the_prime_number_whorl_l28 the_prime_number_whorl_s27 the_prime_number_whorl_s28) (.arrow the_prime_number_whorl_l29 the_prime_number_whorl_s28 the_prime_number_whorl_s29))) (.arrow the_prime_number_whorl_l30 the_prime_number_whorl_s26 the_prime_number_whorl_s30)) (.seq (.arrow the_prime_number_whorl_l31 (tensorProduct the_prime_number_whorl_s29 the_prime_number_whorl_s30) the_prime_number_whorl_s31) (.seq (.arrow the_prime_number_whorl_l32 the_prime_number_whorl_s31 the_prime_number_whorl_s32) (.seq (.arrow the_prime_number_whorl_l33 the_prime_number_whorl_s32 the_prime_number_whorl_s33) (.seq (.arrow the_prime_number_whorl_l34 the_prime_number_whorl_s33 the_prime_number_whorl_s34) (.seq (.arrow the_prime_number_whorl_l35 the_prime_number_whorl_s34 the_prime_number_whorl_s35) (.seq (.arrow the_prime_number_whorl_l36 the_prime_number_whorl_s35 the_prime_number_whorl_s36) (.seq (.arrow the_prime_number_whorl_l37 the_prime_number_whorl_s36 the_prime_number_whorl_s37) (.seq (.arrow the_prime_number_whorl_l38 the_prime_number_whorl_s37 the_prime_number_whorl_s38) (.seq (.arrow the_prime_number_whorl_l39 the_prime_number_whorl_s38 the_prime_number_whorl_s39) (.seq (.arrow the_prime_number_whorl_l40 the_prime_number_whorl_s39 the_prime_number_whorl_s40) (.seq (.arrow the_prime_number_whorl_l41 the_prime_number_whorl_s40 the_prime_number_whorl_s41) (.seq (.arrow the_prime_number_whorl_l42 the_prime_number_whorl_s41 the_prime_number_whorl_s42) (.seq (.arrow the_prime_number_whorl_l43 the_prime_number_whorl_s42 the_prime_number_whorl_s43) (.seq (.arrow the_prime_number_whorl_l44 the_prime_number_whorl_s43 the_prime_number_whorl_s44) (.seq (.arrow the_prime_number_whorl_l45 the_prime_number_whorl_s44 the_prime_number_whorl_s45) (.seq (.arrow the_prime_number_whorl_l46 the_prime_number_whorl_s45 the_prime_number_whorl_s46) (.seq (.arrow the_prime_number_whorl_l47 the_prime_number_whorl_s46 the_prime_number_whorl_s47) (.seq (.arrow the_prime_number_whorl_l48 the_prime_number_whorl_s47 the_prime_number_whorl_s48) (.seq (.arrow the_prime_number_whorl_l49 the_prime_number_whorl_s48 the_prime_number_whorl_s49) (.seq (.arrow the_prime_number_whorl_l50 the_prime_number_whorl_s49 the_prime_number_whorl_s50) (.seq (.arrow the_prime_number_whorl_l51 the_prime_number_whorl_s50 the_prime_number_whorl_s51) (.seq (.arrow the_prime_number_whorl_l52 the_prime_number_whorl_s51 the_prime_number_whorl_s52) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l53 the_prime_number_whorl_s52 the_prime_number_whorl_s53) (.seq (.arrow the_prime_number_whorl_l54 the_prime_number_whorl_s53 the_prime_number_whorl_s54) (.arrow the_prime_number_whorl_l55 the_prime_number_whorl_s54 the_prime_number_whorl_s55))) (.refl the_prime_number_whorl_s52)) (.seq (.arrow the_prime_number_whorl_l56 (tensorProduct the_prime_number_whorl_s55 the_prime_number_whorl_s52) the_prime_number_whorl_s56) (.seq (.arrow the_prime_number_whorl_l57 the_prime_number_whorl_s56 the_prime_number_whorl_s57) (.seq (.arrow the_prime_number_whorl_l58 the_prime_number_whorl_s57 the_prime_number_whorl_s58) (.seq (.arrow the_prime_number_whorl_l59 the_prime_number_whorl_s58 the_prime_number_whorl_s59) (.seq (.arrow the_prime_number_whorl_l60 the_prime_number_whorl_s59 the_prime_number_whorl_s60) (.seq (.arrow the_prime_number_whorl_l61 the_prime_number_whorl_s60 the_prime_number_whorl_s61) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l62 the_prime_number_whorl_s61 the_prime_number_whorl_s62) (.arrow the_prime_number_whorl_l63 the_prime_number_whorl_s62 the_prime_number_whorl_s63)) (.refl the_prime_number_whorl_s61)) (.seq (.arrow the_prime_number_whorl_l64 (tensorProduct the_prime_number_whorl_s63 the_prime_number_whorl_s61) the_prime_number_whorl_s64) (.seq (.arrow the_prime_number_whorl_l65 the_prime_number_whorl_s64 the_prime_number_whorl_s65) (.seq (.arrow the_prime_number_whorl_l66 the_prime_number_whorl_s65 the_prime_number_whorl_s66) (.seq (.arrow the_prime_number_whorl_l67 the_prime_number_whorl_s66 the_prime_number_whorl_s67) (.seq (.arrow the_prime_number_whorl_l68 the_prime_number_whorl_s67 the_prime_number_whorl_s68) (.seq (.arrow the_prime_number_whorl_l69 the_prime_number_whorl_s68 the_prime_number_whorl_s69) (.seq (.arrow the_prime_number_whorl_l70 the_prime_number_whorl_s69 the_prime_number_whorl_s70) (.seq (.arrow the_prime_number_whorl_l71 the_prime_number_whorl_s70 the_prime_number_whorl_s71) (.seq (.arrow the_prime_number_whorl_l72 the_prime_number_whorl_s71 the_prime_number_whorl_s72) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l73 the_prime_number_whorl_s72 the_prime_number_whorl_s73) (.arrow the_prime_number_whorl_l74 the_prime_number_whorl_s73 the_prime_number_whorl_s74)) (.seq (.arrow the_prime_number_whorl_l75 the_prime_number_whorl_s72 the_prime_number_whorl_s75) (.arrow the_prime_number_whorl_l76 the_prime_number_whorl_s75 the_prime_number_whorl_s76))) (.seq (.arrow the_prime_number_whorl_l77 (tensorProduct the_prime_number_whorl_s74 the_prime_number_whorl_s76) the_prime_number_whorl_s77) (.seq (.arrow the_prime_number_whorl_l78 the_prime_number_whorl_s77 the_prime_number_whorl_s78) (.seq (.arrow the_prime_number_whorl_l79 the_prime_number_whorl_s78 the_prime_number_whorl_s79) (.seq (.arrow the_prime_number_whorl_l80 the_prime_number_whorl_s79 the_prime_number_whorl_s80) (.seq (.arrow the_prime_number_whorl_l81 the_prime_number_whorl_s80 the_prime_number_whorl_s81) (.seq (.arrow the_prime_number_whorl_l82 the_prime_number_whorl_s81 the_prime_number_whorl_s82) (.seq (.arrow the_prime_number_whorl_l83 the_prime_number_whorl_s82 the_prime_number_whorl_s83) (.seq (.arrow the_prime_number_whorl_l84 the_prime_number_whorl_s83 the_prime_number_whorl_s84) (.seq (.arrow the_prime_number_whorl_l85 the_prime_number_whorl_s84 the_prime_number_whorl_s85) (.seq (.prod (.arrow the_prime_number_whorl_l86 the_prime_number_whorl_s85 the_prime_number_whorl_s86) (.arrow the_prime_number_whorl_l87 the_prime_number_whorl_s85 the_prime_number_whorl_s87)) (.seq (.arrow the_prime_number_whorl_l88 (tensorProduct the_prime_number_whorl_s86 the_prime_number_whorl_s87) the_prime_number_whorl_s88) (.seq (.arrow the_prime_number_whorl_l89 the_prime_number_whorl_s88 the_prime_number_whorl_s89) (.seq (.arrow the_prime_number_whorl_l90 the_prime_number_whorl_s89 the_prime_number_whorl_s90) (.seq (.arrow the_prime_number_whorl_l91 the_prime_number_whorl_s90 the_prime_number_whorl_s91) (.seq (.arrow the_prime_number_whorl_l92 the_prime_number_whorl_s91 the_prime_number_whorl_s92) (.seq (.arrow the_prime_number_whorl_l93 the_prime_number_whorl_s92 the_prime_number_whorl_s93) (.seq (.arrow the_prime_number_whorl_l94 the_prime_number_whorl_s93 the_prime_number_whorl_s94) (.seq (.arrow the_prime_number_whorl_l95 the_prime_number_whorl_s94 the_prime_number_whorl_s95) (.seq (.arrow the_prime_number_whorl_l96 the_prime_number_whorl_s95 the_prime_number_whorl_s96) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l97 the_prime_number_whorl_s96 the_prime_number_whorl_s97) (.seq (.arrow the_prime_number_whorl_l98 the_prime_number_whorl_s97 the_prime_number_whorl_s98) (.seq (.arrow the_prime_number_whorl_l99 the_prime_number_whorl_s98 the_prime_number_whorl_s99) (.arrow the_prime_number_whorl_l100 the_prime_number_whorl_s99 the_prime_number_whorl_s100)))) (.seq (.arrow the_prime_number_whorl_l101 the_prime_number_whorl_s96 the_prime_number_whorl_s101) (.arrow the_prime_number_whorl_l102 the_prime_number_whorl_s101 the_prime_number_whorl_s102))) (.seq (.arrow the_prime_number_whorl_l103 (tensorProduct the_prime_number_whorl_s100 the_prime_number_whorl_s102) the_prime_number_whorl_s103) (.seq (.arrow the_prime_number_whorl_l104 the_prime_number_whorl_s103 the_prime_number_whorl_s104) (.seq (.arrow the_prime_number_whorl_l105 the_prime_number_whorl_s104 the_prime_number_whorl_s105) (.seq (.arrow the_prime_number_whorl_l106 the_prime_number_whorl_s105 the_prime_number_whorl_s106) (.seq (.arrow the_prime_number_whorl_l107 the_prime_number_whorl_s106 the_prime_number_whorl_s107) (.seq (.arrow the_prime_number_whorl_l108 the_prime_number_whorl_s107 the_prime_number_whorl_s108) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l109 the_prime_number_whorl_s108 the_prime_number_whorl_s109) (.arrow the_prime_number_whorl_l110 the_prime_number_whorl_s109 the_prime_number_whorl_s110)) (.refl the_prime_number_whorl_s108)) (.seq (.arrow the_prime_number_whorl_l111 (tensorProduct the_prime_number_whorl_s110 the_prime_number_whorl_s108) the_prime_number_whorl_s111) (.seq (.arrow the_prime_number_whorl_l112 the_prime_number_whorl_s111 the_prime_number_whorl_s112) (.seq (.arrow the_prime_number_whorl_l113 the_prime_number_whorl_s112 the_prime_number_whorl_s113) (.seq (.arrow the_prime_number_whorl_l114 the_prime_number_whorl_s113 the_prime_number_whorl_s114) (.seq (.arrow the_prime_number_whorl_l115 the_prime_number_whorl_s114 the_prime_number_whorl_s115) (.seq (.arrow the_prime_number_whorl_l116 the_prime_number_whorl_s115 the_prime_number_whorl_s116) (.seq (.arrow the_prime_number_whorl_l117 the_prime_number_whorl_s116 the_prime_number_whorl_s117) (.seq (.arrow the_prime_number_whorl_l118 the_prime_number_whorl_s117 the_prime_number_whorl_s118) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l119 the_prime_number_whorl_s118 the_prime_number_whorl_s119) (.seq (.arrow the_prime_number_whorl_l120 the_prime_number_whorl_s119 the_prime_number_whorl_s120) (.seq (.arrow the_prime_number_whorl_l121 the_prime_number_whorl_s120 the_prime_number_whorl_s121) (.arrow the_prime_number_whorl_l122 the_prime_number_whorl_s121 the_prime_number_whorl_s122)))) (.arrow the_prime_number_whorl_l123 the_prime_number_whorl_s118 the_prime_number_whorl_s123)) (.seq (.arrow the_prime_number_whorl_l124 (tensorProduct the_prime_number_whorl_s122 the_prime_number_whorl_s123) the_prime_number_whorl_s124) (.seq (.arrow the_prime_number_whorl_l125 the_prime_number_whorl_s124 the_prime_number_whorl_s125) (.seq (.arrow the_prime_number_whorl_l126 the_prime_number_whorl_s125 the_prime_number_whorl_s126) (.seq (.arrow the_prime_number_whorl_l127 the_prime_number_whorl_s126 the_prime_number_whorl_s127) (.seq (.arrow the_prime_number_whorl_l128 the_prime_number_whorl_s127 the_prime_number_whorl_s128) (.seq (.arrow the_prime_number_whorl_l129 the_prime_number_whorl_s128 the_prime_number_whorl_s129) (.seq (.arrow the_prime_number_whorl_l130 the_prime_number_whorl_s129 the_prime_number_whorl_s130) (.seq (.arrow the_prime_number_whorl_l131 the_prime_number_whorl_s130 the_prime_number_whorl_s131) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l132 the_prime_number_whorl_s131 the_prime_number_whorl_s132) (.arrow the_prime_number_whorl_l133 the_prime_number_whorl_s132 the_prime_number_whorl_s133)) (.arrow the_prime_number_whorl_l134 the_prime_number_whorl_s131 the_prime_number_whorl_s134)) (.seq (.arrow the_prime_number_whorl_l135 (tensorProduct the_prime_number_whorl_s133 the_prime_number_whorl_s134) the_prime_number_whorl_s135) (.seq (.arrow the_prime_number_whorl_l136 the_prime_number_whorl_s135 the_prime_number_whorl_s136) (.seq (.prod (.refl the_prime_number_whorl_s136) (.arrow the_prime_number_whorl_l137 the_prime_number_whorl_s136 the_prime_number_whorl_s137)) (.seq (.arrow the_prime_number_whorl_l138 (tensorProduct the_prime_number_whorl_s136 the_prime_number_whorl_s137) the_prime_number_whorl_s138) (.seq (.arrow the_prime_number_whorl_l139 the_prime_number_whorl_s138 the_prime_number_whorl_s139) (.seq (.arrow the_prime_number_whorl_l140 the_prime_number_whorl_s139 the_prime_number_whorl_s140) (.seq (.arrow the_prime_number_whorl_l141 the_prime_number_whorl_s140 the_prime_number_whorl_s141) (.seq (.arrow the_prime_number_whorl_l142 the_prime_number_whorl_s141 the_prime_number_whorl_s142) (.seq (.arrow the_prime_number_whorl_l143 the_prime_number_whorl_s142 the_prime_number_whorl_s143) (.seq (.arrow the_prime_number_whorl_l144 the_prime_number_whorl_s143 the_prime_number_whorl_s144) (.seq (.arrow the_prime_number_whorl_l145 the_prime_number_whorl_s144 the_prime_number_whorl_s145) (.seq (.prod (.seq (.arrow the_prime_number_whorl_l146 the_prime_number_whorl_s145 the_prime_number_whorl_s146) (.arrow the_prime_number_whorl_l147 the_prime_number_whorl_s146 the_prime_number_whorl_s147)) (.refl the_prime_number_whorl_s145)) (.seq (.arrow the_prime_number_whorl_l148 (tensorProduct the_prime_number_whorl_s147 the_prime_number_whorl_s145) the_prime_number_whorl_s148) (.seq (.arrow the_prime_number_whorl_l149 the_prime_number_whorl_s148 the_prime_number_whorl_s149) (.seq (.arrow the_prime_number_whorl_l150 the_prime_number_whorl_s149 the_prime_number_whorl_s150) (.arrow the_prime_number_whorl_l151 the_prime_number_whorl_s150 the_prime_number_whorl_s151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_prime_number_whorl_true_arm : IGProtocol the_prime_number_whorl_initial the_prime_number_whorl_s151 :=
  (the_prime_number_whorl_protocol).restrictToEVALT

-- false arm
noncomputable def the_prime_number_whorl_false_arm : IGProtocol the_prime_number_whorl_initial the_prime_number_whorl_s151 :=
  (the_prime_number_whorl_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_prime_number_whorl_tier_ground : OuroboricityTier := TierFunctor.obj the_prime_number_whorl_initial
def the_prime_number_whorl_tier : OuroboricityTier := TierFunctor.obj the_prime_number_whorl_s151
#eval the_prime_number_whorl_tier_ground  -- tier of the ground (pre-transformation)
#eval the_prime_number_whorl_tier  -- the Grammar's tuple-tier verdict

theorem the_prime_number_whorl_protocol_depth :
    the_prime_number_whorl_protocol.depth = 141 := by rfl

end Imscribing