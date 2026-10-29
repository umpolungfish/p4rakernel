-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊙ → ≺ → ⊥ → ∋ → ⊙ → ∈ → ⊥ → ≺ → ⊞ → ∋ → ⋈ → ⊙ → ≺ → ⋈ → ⊙ → ≻ → ≻ → ⋈ → ⊤ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊤ → ≻ → ⋈ → ≺ → ⋈ → ⊙ → ⋈ → ⊥ → ≻ → ⊞ → ∋ → ⋈ → ≺ → ∋ → ⋈ → ⊙ → ⋈ → ⊣
-- Class: imasm_hotswaps
-- Fingerprint: sig=(123,22,31,0)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=176
-- Expected tier: O₁
-- ∈/∋ pairs: [(2, 9), (11, 15)]

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
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [12] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [13] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [14] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [15] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [16] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [17] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [18] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [19] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [20] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [21] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [25] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [26] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [27] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [28] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [29] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [30] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [31] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [32] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [33] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [34] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [35] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [36] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [37] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [38] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [39] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [40] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [41] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [42] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [43] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [44] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [45] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [46] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [47] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [48] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [49] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [52] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [53] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [54] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [55] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [56] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [57] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [58] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [59] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [60] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [61] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [62] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [63] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [64] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [65] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [66] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [67] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [68] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [69] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [70] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [71] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [72] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [73] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [74] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [75] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [76] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [77] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [78] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [79] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [80] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [81] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [82] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [83] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [84] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [85] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [86] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [87] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [88] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [89] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [90] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [91] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [92] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [93] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [94] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [95] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [96] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [97] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [98] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [99] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [100] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [101] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [102] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [103] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [104] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [105] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [106] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [107] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [108] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [109] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [110] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [111] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [112] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [113] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [114] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [115] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [116] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [117] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [118] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [119] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [120] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [121] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [122] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [123] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [124] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [125] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [126] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [127] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [128] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [129] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [130] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [131] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [132] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [133] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [134] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [135] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [136] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [137] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [138] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [139] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [140] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [141] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [142] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [143] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [144] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [145] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [146] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [147] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [148] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [149] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [150] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [151] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [152] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [153] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [154] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [155] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [156] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [157] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [158] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [159] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [160] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [161] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [162] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [163] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [164] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [165] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [166] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [167] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [168] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [169] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [170] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [171] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [172] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [173] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [174] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [175] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def imasm_hotswaps_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s100 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s101 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s102 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s103 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s104 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s105 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s106 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s107 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s108 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s109 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s110 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s111 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s112 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s113 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s114 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s115 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s116 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s117 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s118 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s119 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s120 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s121 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s122 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s123 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s124 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s125 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s126 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s127 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s128 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s129 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s130 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s131 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s132 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s133 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s134 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s135 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s136 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s137 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s138 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s139 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s140 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s141 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s142 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s143 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s144 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s145 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s146 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s147 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s148 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s149 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s150 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s151 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s152 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s153 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s154 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s155 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s156 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s157 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s158 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s159 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s160 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s161 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s162 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s163 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s164 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s165 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s166 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s167 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def imasm_hotswaps_s168 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s169 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s170 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s171 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s172 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s173 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s174 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_s175 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def imasm_hotswaps_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l30 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l40 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l47 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l57 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l64 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l74 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l81 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l82 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l84 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l90 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l91 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l93 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l94 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l95 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l96 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l98 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l100 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l101 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l102 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l103 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l104 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l105 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l106 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l107 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l108 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l109 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l110 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l111 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l112 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l113 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l114 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l115 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l116 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l117 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l118 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l119 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l120 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l121 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l122 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l123 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l124 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l125 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l126 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l127 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l128 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l129 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l130 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l131 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l132 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l133 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l134 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l135 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l136 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l137 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l138 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l139 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l140 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l141 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l142 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l143 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l144 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l145 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l146 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l147 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l148 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l149 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l150 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l151 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l152 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l153 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l154 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l155 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l156 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l157 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l158 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l159 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l160 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l161 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l162 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l163 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l164 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l165 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def imasm_hotswaps_l166 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l167 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def imasm_hotswaps_l168 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l169 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l170 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l171 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l172 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l173 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l174 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def imasm_hotswaps_l175 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def imasm_hotswaps_protocol : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s175 :=
  .withGram Grammar.measure <|
  (.seq (.arrow imasm_hotswaps_l0 imasm_hotswaps_initial imasm_hotswaps_s0) (.seq (.arrow imasm_hotswaps_l1 imasm_hotswaps_s0 imasm_hotswaps_s1) (.seq (.arrow imasm_hotswaps_l2 imasm_hotswaps_s1 imasm_hotswaps_s2) (.seq (.prod (.seq (.arrow imasm_hotswaps_l3 imasm_hotswaps_s2 imasm_hotswaps_s3) (.seq (.arrow imasm_hotswaps_l4 imasm_hotswaps_s3 imasm_hotswaps_s4) (.seq (.arrow imasm_hotswaps_l5 imasm_hotswaps_s4 imasm_hotswaps_s5) (.seq (.arrow imasm_hotswaps_l6 imasm_hotswaps_s5 imasm_hotswaps_s6) (.arrow imasm_hotswaps_l7 imasm_hotswaps_s6 imasm_hotswaps_s7))))) (.arrow imasm_hotswaps_l8 imasm_hotswaps_s2 imasm_hotswaps_s8)) (.seq (.arrow imasm_hotswaps_l9 (tensorProduct imasm_hotswaps_s7 imasm_hotswaps_s8) imasm_hotswaps_s9) (.seq (.arrow imasm_hotswaps_l10 imasm_hotswaps_s9 imasm_hotswaps_s10) (.seq (.arrow imasm_hotswaps_l11 imasm_hotswaps_s10 imasm_hotswaps_s11) (.seq (.prod (.refl imasm_hotswaps_s11) (.seq (.arrow imasm_hotswaps_l12 imasm_hotswaps_s11 imasm_hotswaps_s12) (.seq (.arrow imasm_hotswaps_l13 imasm_hotswaps_s12 imasm_hotswaps_s13) (.arrow imasm_hotswaps_l14 imasm_hotswaps_s13 imasm_hotswaps_s14)))) (.seq (.arrow imasm_hotswaps_l15 (tensorProduct imasm_hotswaps_s11 imasm_hotswaps_s14) imasm_hotswaps_s15) (.seq (.arrow imasm_hotswaps_l16 imasm_hotswaps_s15 imasm_hotswaps_s16) (.seq (.arrow imasm_hotswaps_l17 imasm_hotswaps_s16 imasm_hotswaps_s17) (.seq (.arrow imasm_hotswaps_l18 imasm_hotswaps_s17 imasm_hotswaps_s18) (.seq (.arrow imasm_hotswaps_l19 imasm_hotswaps_s18 imasm_hotswaps_s19) (.seq (.arrow imasm_hotswaps_l20 imasm_hotswaps_s19 imasm_hotswaps_s20) (.seq (.arrow imasm_hotswaps_l21 imasm_hotswaps_s20 imasm_hotswaps_s21) (.seq (.arrow imasm_hotswaps_l22 imasm_hotswaps_s21 imasm_hotswaps_s22) (.seq (.arrow imasm_hotswaps_l23 imasm_hotswaps_s22 imasm_hotswaps_s23) (.seq (.arrow imasm_hotswaps_l24 imasm_hotswaps_s23 imasm_hotswaps_s24) (.seq (.arrow imasm_hotswaps_l25 imasm_hotswaps_s24 imasm_hotswaps_s25) (.seq (.arrow imasm_hotswaps_l26 imasm_hotswaps_s25 imasm_hotswaps_s26) (.seq (.arrow imasm_hotswaps_l27 imasm_hotswaps_s26 imasm_hotswaps_s27) (.seq (.arrow imasm_hotswaps_l28 imasm_hotswaps_s27 imasm_hotswaps_s28) (.seq (.arrow imasm_hotswaps_l29 imasm_hotswaps_s28 imasm_hotswaps_s29) (.seq (.arrow imasm_hotswaps_l30 imasm_hotswaps_s29 imasm_hotswaps_s30) (.seq (.arrow imasm_hotswaps_l31 imasm_hotswaps_s30 imasm_hotswaps_s31) (.seq (.arrow imasm_hotswaps_l32 imasm_hotswaps_s31 imasm_hotswaps_s32) (.seq (.arrow imasm_hotswaps_l33 imasm_hotswaps_s32 imasm_hotswaps_s33) (.seq (.arrow imasm_hotswaps_l34 imasm_hotswaps_s33 imasm_hotswaps_s34) (.seq (.arrow imasm_hotswaps_l35 imasm_hotswaps_s34 imasm_hotswaps_s35) (.seq (.arrow imasm_hotswaps_l36 imasm_hotswaps_s35 imasm_hotswaps_s36) (.seq (.arrow imasm_hotswaps_l37 imasm_hotswaps_s36 imasm_hotswaps_s37) (.seq (.arrow imasm_hotswaps_l38 imasm_hotswaps_s37 imasm_hotswaps_s38) (.seq (.arrow imasm_hotswaps_l39 imasm_hotswaps_s38 imasm_hotswaps_s39) (.seq (.arrow imasm_hotswaps_l40 imasm_hotswaps_s39 imasm_hotswaps_s40) (.seq (.arrow imasm_hotswaps_l41 imasm_hotswaps_s40 imasm_hotswaps_s41) (.seq (.arrow imasm_hotswaps_l42 imasm_hotswaps_s41 imasm_hotswaps_s42) (.seq (.arrow imasm_hotswaps_l43 imasm_hotswaps_s42 imasm_hotswaps_s43) (.seq (.arrow imasm_hotswaps_l44 imasm_hotswaps_s43 imasm_hotswaps_s44) (.seq (.arrow imasm_hotswaps_l45 imasm_hotswaps_s44 imasm_hotswaps_s45) (.seq (.arrow imasm_hotswaps_l46 imasm_hotswaps_s45 imasm_hotswaps_s46) (.seq (.arrow imasm_hotswaps_l47 imasm_hotswaps_s46 imasm_hotswaps_s47) (.seq (.arrow imasm_hotswaps_l48 imasm_hotswaps_s47 imasm_hotswaps_s48) (.seq (.arrow imasm_hotswaps_l49 imasm_hotswaps_s48 imasm_hotswaps_s49) (.seq (.arrow imasm_hotswaps_l50 imasm_hotswaps_s49 imasm_hotswaps_s50) (.seq (.arrow imasm_hotswaps_l51 imasm_hotswaps_s50 imasm_hotswaps_s51) (.seq (.arrow imasm_hotswaps_l52 imasm_hotswaps_s51 imasm_hotswaps_s52) (.seq (.arrow imasm_hotswaps_l53 imasm_hotswaps_s52 imasm_hotswaps_s53) (.seq (.arrow imasm_hotswaps_l54 imasm_hotswaps_s53 imasm_hotswaps_s54) (.seq (.arrow imasm_hotswaps_l55 imasm_hotswaps_s54 imasm_hotswaps_s55) (.seq (.arrow imasm_hotswaps_l56 imasm_hotswaps_s55 imasm_hotswaps_s56) (.seq (.arrow imasm_hotswaps_l57 imasm_hotswaps_s56 imasm_hotswaps_s57) (.seq (.arrow imasm_hotswaps_l58 imasm_hotswaps_s57 imasm_hotswaps_s58) (.seq (.arrow imasm_hotswaps_l59 imasm_hotswaps_s58 imasm_hotswaps_s59) (.seq (.arrow imasm_hotswaps_l60 imasm_hotswaps_s59 imasm_hotswaps_s60) (.seq (.arrow imasm_hotswaps_l61 imasm_hotswaps_s60 imasm_hotswaps_s61) (.seq (.arrow imasm_hotswaps_l62 imasm_hotswaps_s61 imasm_hotswaps_s62) (.seq (.arrow imasm_hotswaps_l63 imasm_hotswaps_s62 imasm_hotswaps_s63) (.seq (.arrow imasm_hotswaps_l64 imasm_hotswaps_s63 imasm_hotswaps_s64) (.seq (.arrow imasm_hotswaps_l65 imasm_hotswaps_s64 imasm_hotswaps_s65) (.seq (.arrow imasm_hotswaps_l66 imasm_hotswaps_s65 imasm_hotswaps_s66) (.seq (.arrow imasm_hotswaps_l67 imasm_hotswaps_s66 imasm_hotswaps_s67) (.seq (.arrow imasm_hotswaps_l68 imasm_hotswaps_s67 imasm_hotswaps_s68) (.seq (.arrow imasm_hotswaps_l69 imasm_hotswaps_s68 imasm_hotswaps_s69) (.seq (.arrow imasm_hotswaps_l70 imasm_hotswaps_s69 imasm_hotswaps_s70) (.seq (.arrow imasm_hotswaps_l71 imasm_hotswaps_s70 imasm_hotswaps_s71) (.seq (.arrow imasm_hotswaps_l72 imasm_hotswaps_s71 imasm_hotswaps_s72) (.seq (.arrow imasm_hotswaps_l73 imasm_hotswaps_s72 imasm_hotswaps_s73) (.seq (.arrow imasm_hotswaps_l74 imasm_hotswaps_s73 imasm_hotswaps_s74) (.seq (.arrow imasm_hotswaps_l75 imasm_hotswaps_s74 imasm_hotswaps_s75) (.seq (.arrow imasm_hotswaps_l76 imasm_hotswaps_s75 imasm_hotswaps_s76) (.seq (.arrow imasm_hotswaps_l77 imasm_hotswaps_s76 imasm_hotswaps_s77) (.seq (.arrow imasm_hotswaps_l78 imasm_hotswaps_s77 imasm_hotswaps_s78) (.seq (.arrow imasm_hotswaps_l79 imasm_hotswaps_s78 imasm_hotswaps_s79) (.seq (.arrow imasm_hotswaps_l80 imasm_hotswaps_s79 imasm_hotswaps_s80) (.seq (.arrow imasm_hotswaps_l81 imasm_hotswaps_s80 imasm_hotswaps_s81) (.seq (.arrow imasm_hotswaps_l82 imasm_hotswaps_s81 imasm_hotswaps_s82) (.seq (.arrow imasm_hotswaps_l83 imasm_hotswaps_s82 imasm_hotswaps_s83) (.seq (.arrow imasm_hotswaps_l84 imasm_hotswaps_s83 imasm_hotswaps_s84) (.seq (.arrow imasm_hotswaps_l85 imasm_hotswaps_s84 imasm_hotswaps_s85) (.seq (.arrow imasm_hotswaps_l86 imasm_hotswaps_s85 imasm_hotswaps_s86) (.seq (.arrow imasm_hotswaps_l87 imasm_hotswaps_s86 imasm_hotswaps_s87) (.seq (.arrow imasm_hotswaps_l88 imasm_hotswaps_s87 imasm_hotswaps_s88) (.seq (.arrow imasm_hotswaps_l89 imasm_hotswaps_s88 imasm_hotswaps_s89) (.seq (.arrow imasm_hotswaps_l90 imasm_hotswaps_s89 imasm_hotswaps_s90) (.seq (.arrow imasm_hotswaps_l91 imasm_hotswaps_s90 imasm_hotswaps_s91) (.seq (.arrow imasm_hotswaps_l92 imasm_hotswaps_s91 imasm_hotswaps_s92) (.seq (.arrow imasm_hotswaps_l93 imasm_hotswaps_s92 imasm_hotswaps_s93) (.seq (.arrow imasm_hotswaps_l94 imasm_hotswaps_s93 imasm_hotswaps_s94) (.seq (.arrow imasm_hotswaps_l95 imasm_hotswaps_s94 imasm_hotswaps_s95) (.seq (.arrow imasm_hotswaps_l96 imasm_hotswaps_s95 imasm_hotswaps_s96) (.seq (.arrow imasm_hotswaps_l97 imasm_hotswaps_s96 imasm_hotswaps_s97) (.seq (.arrow imasm_hotswaps_l98 imasm_hotswaps_s97 imasm_hotswaps_s98) (.seq (.arrow imasm_hotswaps_l99 imasm_hotswaps_s98 imasm_hotswaps_s99) (.seq (.arrow imasm_hotswaps_l100 imasm_hotswaps_s99 imasm_hotswaps_s100) (.seq (.arrow imasm_hotswaps_l101 imasm_hotswaps_s100 imasm_hotswaps_s101) (.seq (.arrow imasm_hotswaps_l102 imasm_hotswaps_s101 imasm_hotswaps_s102) (.seq (.arrow imasm_hotswaps_l103 imasm_hotswaps_s102 imasm_hotswaps_s103) (.seq (.arrow imasm_hotswaps_l104 imasm_hotswaps_s103 imasm_hotswaps_s104) (.seq (.arrow imasm_hotswaps_l105 imasm_hotswaps_s104 imasm_hotswaps_s105) (.seq (.arrow imasm_hotswaps_l106 imasm_hotswaps_s105 imasm_hotswaps_s106) (.seq (.arrow imasm_hotswaps_l107 imasm_hotswaps_s106 imasm_hotswaps_s107) (.seq (.arrow imasm_hotswaps_l108 imasm_hotswaps_s107 imasm_hotswaps_s108) (.seq (.arrow imasm_hotswaps_l109 imasm_hotswaps_s108 imasm_hotswaps_s109) (.seq (.arrow imasm_hotswaps_l110 imasm_hotswaps_s109 imasm_hotswaps_s110) (.seq (.arrow imasm_hotswaps_l111 imasm_hotswaps_s110 imasm_hotswaps_s111) (.seq (.arrow imasm_hotswaps_l112 imasm_hotswaps_s111 imasm_hotswaps_s112) (.seq (.arrow imasm_hotswaps_l113 imasm_hotswaps_s112 imasm_hotswaps_s113) (.seq (.arrow imasm_hotswaps_l114 imasm_hotswaps_s113 imasm_hotswaps_s114) (.seq (.arrow imasm_hotswaps_l115 imasm_hotswaps_s114 imasm_hotswaps_s115) (.seq (.arrow imasm_hotswaps_l116 imasm_hotswaps_s115 imasm_hotswaps_s116) (.seq (.arrow imasm_hotswaps_l117 imasm_hotswaps_s116 imasm_hotswaps_s117) (.seq (.arrow imasm_hotswaps_l118 imasm_hotswaps_s117 imasm_hotswaps_s118) (.seq (.arrow imasm_hotswaps_l119 imasm_hotswaps_s118 imasm_hotswaps_s119) (.seq (.arrow imasm_hotswaps_l120 imasm_hotswaps_s119 imasm_hotswaps_s120) (.seq (.arrow imasm_hotswaps_l121 imasm_hotswaps_s120 imasm_hotswaps_s121) (.seq (.arrow imasm_hotswaps_l122 imasm_hotswaps_s121 imasm_hotswaps_s122) (.seq (.arrow imasm_hotswaps_l123 imasm_hotswaps_s122 imasm_hotswaps_s123) (.seq (.arrow imasm_hotswaps_l124 imasm_hotswaps_s123 imasm_hotswaps_s124) (.seq (.arrow imasm_hotswaps_l125 imasm_hotswaps_s124 imasm_hotswaps_s125) (.seq (.arrow imasm_hotswaps_l126 imasm_hotswaps_s125 imasm_hotswaps_s126) (.seq (.arrow imasm_hotswaps_l127 imasm_hotswaps_s126 imasm_hotswaps_s127) (.seq (.arrow imasm_hotswaps_l128 imasm_hotswaps_s127 imasm_hotswaps_s128) (.seq (.arrow imasm_hotswaps_l129 imasm_hotswaps_s128 imasm_hotswaps_s129) (.seq (.arrow imasm_hotswaps_l130 imasm_hotswaps_s129 imasm_hotswaps_s130) (.seq (.arrow imasm_hotswaps_l131 imasm_hotswaps_s130 imasm_hotswaps_s131) (.seq (.arrow imasm_hotswaps_l132 imasm_hotswaps_s131 imasm_hotswaps_s132) (.seq (.arrow imasm_hotswaps_l133 imasm_hotswaps_s132 imasm_hotswaps_s133) (.seq (.arrow imasm_hotswaps_l134 imasm_hotswaps_s133 imasm_hotswaps_s134) (.seq (.arrow imasm_hotswaps_l135 imasm_hotswaps_s134 imasm_hotswaps_s135) (.seq (.arrow imasm_hotswaps_l136 imasm_hotswaps_s135 imasm_hotswaps_s136) (.seq (.arrow imasm_hotswaps_l137 imasm_hotswaps_s136 imasm_hotswaps_s137) (.seq (.arrow imasm_hotswaps_l138 imasm_hotswaps_s137 imasm_hotswaps_s138) (.seq (.arrow imasm_hotswaps_l139 imasm_hotswaps_s138 imasm_hotswaps_s139) (.seq (.arrow imasm_hotswaps_l140 imasm_hotswaps_s139 imasm_hotswaps_s140) (.seq (.arrow imasm_hotswaps_l141 imasm_hotswaps_s140 imasm_hotswaps_s141) (.seq (.arrow imasm_hotswaps_l142 imasm_hotswaps_s141 imasm_hotswaps_s142) (.seq (.arrow imasm_hotswaps_l143 imasm_hotswaps_s142 imasm_hotswaps_s143) (.seq (.arrow imasm_hotswaps_l144 imasm_hotswaps_s143 imasm_hotswaps_s144) (.seq (.arrow imasm_hotswaps_l145 imasm_hotswaps_s144 imasm_hotswaps_s145) (.seq (.arrow imasm_hotswaps_l146 imasm_hotswaps_s145 imasm_hotswaps_s146) (.seq (.arrow imasm_hotswaps_l147 imasm_hotswaps_s146 imasm_hotswaps_s147) (.seq (.arrow imasm_hotswaps_l148 imasm_hotswaps_s147 imasm_hotswaps_s148) (.seq (.arrow imasm_hotswaps_l149 imasm_hotswaps_s148 imasm_hotswaps_s149) (.seq (.arrow imasm_hotswaps_l150 imasm_hotswaps_s149 imasm_hotswaps_s150) (.seq (.arrow imasm_hotswaps_l151 imasm_hotswaps_s150 imasm_hotswaps_s151) (.seq (.arrow imasm_hotswaps_l152 imasm_hotswaps_s151 imasm_hotswaps_s152) (.seq (.arrow imasm_hotswaps_l153 imasm_hotswaps_s152 imasm_hotswaps_s153) (.seq (.arrow imasm_hotswaps_l154 imasm_hotswaps_s153 imasm_hotswaps_s154) (.seq (.arrow imasm_hotswaps_l155 imasm_hotswaps_s154 imasm_hotswaps_s155) (.seq (.arrow imasm_hotswaps_l156 imasm_hotswaps_s155 imasm_hotswaps_s156) (.seq (.arrow imasm_hotswaps_l157 imasm_hotswaps_s156 imasm_hotswaps_s157) (.seq (.arrow imasm_hotswaps_l158 imasm_hotswaps_s157 imasm_hotswaps_s158) (.seq (.arrow imasm_hotswaps_l159 imasm_hotswaps_s158 imasm_hotswaps_s159) (.seq (.arrow imasm_hotswaps_l160 imasm_hotswaps_s159 imasm_hotswaps_s160) (.seq (.arrow imasm_hotswaps_l161 imasm_hotswaps_s160 imasm_hotswaps_s161) (.seq (.arrow imasm_hotswaps_l162 imasm_hotswaps_s161 imasm_hotswaps_s162) (.seq (.arrow imasm_hotswaps_l163 imasm_hotswaps_s162 imasm_hotswaps_s163) (.seq (.arrow imasm_hotswaps_l164 imasm_hotswaps_s163 imasm_hotswaps_s164) (.seq (.arrow imasm_hotswaps_l165 imasm_hotswaps_s164 imasm_hotswaps_s165) (.seq (.arrow imasm_hotswaps_l166 imasm_hotswaps_s165 imasm_hotswaps_s166) (.seq (.arrow imasm_hotswaps_l167 imasm_hotswaps_s166 imasm_hotswaps_s167) (.seq (.arrow imasm_hotswaps_l168 imasm_hotswaps_s167 imasm_hotswaps_s168) (.seq (.arrow imasm_hotswaps_l169 imasm_hotswaps_s168 imasm_hotswaps_s169) (.seq (.arrow imasm_hotswaps_l170 imasm_hotswaps_s169 imasm_hotswaps_s170) (.seq (.arrow imasm_hotswaps_l171 imasm_hotswaps_s170 imasm_hotswaps_s171) (.seq (.arrow imasm_hotswaps_l172 imasm_hotswaps_s171 imasm_hotswaps_s172) (.seq (.arrow imasm_hotswaps_l173 imasm_hotswaps_s172 imasm_hotswaps_s173) (.seq (.arrow imasm_hotswaps_l174 imasm_hotswaps_s173 imasm_hotswaps_s174) (.arrow imasm_hotswaps_l175 imasm_hotswaps_s174 imasm_hotswaps_s175)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def imasm_hotswaps_true_arm : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s175 :=
  (imasm_hotswaps_protocol).restrictToEVALT

-- false arm
noncomputable def imasm_hotswaps_false_arm : IGProtocol imasm_hotswaps_initial imasm_hotswaps_s175 :=
  (imasm_hotswaps_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def imasm_hotswaps_tier_ground : OuroboricityTier := TierFunctor.obj imasm_hotswaps_initial
def imasm_hotswaps_tier : OuroboricityTier := TierFunctor.obj imasm_hotswaps_s175
#eval imasm_hotswaps_tier_ground  -- tier of the ground (pre-transformation)
#eval imasm_hotswaps_tier  -- the Grammar's tuple-tier verdict

theorem imasm_hotswaps_protocol_depth :
    imasm_hotswaps_protocol.depth = 175 := by rfl

end Imscribing