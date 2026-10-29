-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⋈ → ⊤ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊙ → ∋ → ⊣
-- Class: Z_boson
-- Fingerprint: sig=(65,2,33,4)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=104
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 102)]

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
--   [10] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [13] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [14] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [15] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [18] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [19] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [20] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [21] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [22] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [23] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [24] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [27] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [28] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [29] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [30] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [31] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [32] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [33] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [34] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [35] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [36] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [37] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [38] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [39] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [40] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [41] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [42] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [43] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [44] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [45] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [46] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [47] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [52] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [53] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [54] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [55] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [56] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [57] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [58] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [59] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [60] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [61] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [62] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [63] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [64] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [65] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [66] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [67] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [68] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [69] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [70] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [71] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [72] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [73] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [74] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [75] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [76] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [77] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [78] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [79] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [80] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [81] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [82] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [83] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [84] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [85] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [86] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [87] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [88] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [89] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [90] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [91] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [92] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [93] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [94] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [95] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [96] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [97] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [98] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [99] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [100] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [101] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [102] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [103] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def z_boson_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def z_boson_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def z_boson_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def z_boson_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def z_boson_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def z_boson_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s80 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s81 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s82 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s83 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s84 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s85 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s86 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s87 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s88 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s89 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s90 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s91 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s92 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s93 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s94 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s95 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s96 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s97 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s98 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s99 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s100 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s101 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def z_boson_s102 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def z_boson_s103 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def z_boson_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def z_boson_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def z_boson_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def z_boson_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l15 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def z_boson_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def z_boson_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l23 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def z_boson_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l30 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l36 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l42 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l54 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l60 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l66 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l72 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l78 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l80 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l81 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l82 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l83 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l84 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l85 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l86 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l87 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l88 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l89 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l90 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l91 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l92 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l93 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l94 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l95 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l96 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l97 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def z_boson_l98 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l99 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l100 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def z_boson_l101 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l102 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def z_boson_l103 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def z_boson_protocol : IGProtocol z_boson_initial z_boson_s103 :=
  .withGram Grammar.measure <|
  (.seq (.arrow z_boson_l0 z_boson_initial z_boson_s0) (.seq (.arrow z_boson_l1 z_boson_s0 z_boson_s1) (.seq (.arrow z_boson_l2 z_boson_s1 z_boson_s2) (.seq (.arrow z_boson_l3 z_boson_s2 z_boson_s3) (.seq (.arrow z_boson_l4 z_boson_s3 z_boson_s4) (.seq (.prod (.seq (.arrow z_boson_l5 z_boson_s4 z_boson_s5) (.seq (.arrow z_boson_l6 z_boson_s5 z_boson_s6) (.seq (.arrow z_boson_l7 z_boson_s6 z_boson_s7) (.seq (.arrow z_boson_l8 z_boson_s7 z_boson_s8) (.seq (.arrow z_boson_l9 z_boson_s8 z_boson_s9) (.seq (.arrow z_boson_l10 z_boson_s9 z_boson_s10) (.arrow z_boson_l11 z_boson_s10 z_boson_s11))))))) (.seq (.arrow z_boson_l12 z_boson_s4 z_boson_s12) (.seq (.arrow z_boson_l13 z_boson_s12 z_boson_s13) (.seq (.arrow z_boson_l14 z_boson_s13 z_boson_s14) (.seq (.arrow z_boson_l15 z_boson_s14 z_boson_s15) (.seq (.arrow z_boson_l16 z_boson_s15 z_boson_s16) (.seq (.arrow z_boson_l17 z_boson_s16 z_boson_s17) (.seq (.arrow z_boson_l18 z_boson_s17 z_boson_s18) (.seq (.arrow z_boson_l19 z_boson_s18 z_boson_s19) (.seq (.arrow z_boson_l20 z_boson_s19 z_boson_s20) (.seq (.arrow z_boson_l21 z_boson_s20 z_boson_s21) (.seq (.arrow z_boson_l22 z_boson_s21 z_boson_s22) (.seq (.arrow z_boson_l23 z_boson_s22 z_boson_s23) (.seq (.arrow z_boson_l24 z_boson_s23 z_boson_s24) (.seq (.arrow z_boson_l25 z_boson_s24 z_boson_s25) (.seq (.arrow z_boson_l26 z_boson_s25 z_boson_s26) (.seq (.arrow z_boson_l27 z_boson_s26 z_boson_s27) (.seq (.arrow z_boson_l28 z_boson_s27 z_boson_s28) (.seq (.arrow z_boson_l29 z_boson_s28 z_boson_s29) (.seq (.arrow z_boson_l30 z_boson_s29 z_boson_s30) (.seq (.arrow z_boson_l31 z_boson_s30 z_boson_s31) (.seq (.arrow z_boson_l32 z_boson_s31 z_boson_s32) (.seq (.arrow z_boson_l33 z_boson_s32 z_boson_s33) (.seq (.arrow z_boson_l34 z_boson_s33 z_boson_s34) (.seq (.arrow z_boson_l35 z_boson_s34 z_boson_s35) (.seq (.arrow z_boson_l36 z_boson_s35 z_boson_s36) (.seq (.arrow z_boson_l37 z_boson_s36 z_boson_s37) (.seq (.arrow z_boson_l38 z_boson_s37 z_boson_s38) (.seq (.arrow z_boson_l39 z_boson_s38 z_boson_s39) (.seq (.arrow z_boson_l40 z_boson_s39 z_boson_s40) (.seq (.arrow z_boson_l41 z_boson_s40 z_boson_s41) (.seq (.arrow z_boson_l42 z_boson_s41 z_boson_s42) (.seq (.arrow z_boson_l43 z_boson_s42 z_boson_s43) (.seq (.arrow z_boson_l44 z_boson_s43 z_boson_s44) (.seq (.arrow z_boson_l45 z_boson_s44 z_boson_s45) (.seq (.arrow z_boson_l46 z_boson_s45 z_boson_s46) (.seq (.arrow z_boson_l47 z_boson_s46 z_boson_s47) (.seq (.arrow z_boson_l48 z_boson_s47 z_boson_s48) (.seq (.arrow z_boson_l49 z_boson_s48 z_boson_s49) (.seq (.arrow z_boson_l50 z_boson_s49 z_boson_s50) (.seq (.arrow z_boson_l51 z_boson_s50 z_boson_s51) (.seq (.arrow z_boson_l52 z_boson_s51 z_boson_s52) (.seq (.arrow z_boson_l53 z_boson_s52 z_boson_s53) (.seq (.arrow z_boson_l54 z_boson_s53 z_boson_s54) (.seq (.arrow z_boson_l55 z_boson_s54 z_boson_s55) (.seq (.arrow z_boson_l56 z_boson_s55 z_boson_s56) (.seq (.arrow z_boson_l57 z_boson_s56 z_boson_s57) (.seq (.arrow z_boson_l58 z_boson_s57 z_boson_s58) (.seq (.arrow z_boson_l59 z_boson_s58 z_boson_s59) (.seq (.arrow z_boson_l60 z_boson_s59 z_boson_s60) (.seq (.arrow z_boson_l61 z_boson_s60 z_boson_s61) (.seq (.arrow z_boson_l62 z_boson_s61 z_boson_s62) (.seq (.arrow z_boson_l63 z_boson_s62 z_boson_s63) (.seq (.arrow z_boson_l64 z_boson_s63 z_boson_s64) (.seq (.arrow z_boson_l65 z_boson_s64 z_boson_s65) (.seq (.arrow z_boson_l66 z_boson_s65 z_boson_s66) (.seq (.arrow z_boson_l67 z_boson_s66 z_boson_s67) (.seq (.arrow z_boson_l68 z_boson_s67 z_boson_s68) (.seq (.arrow z_boson_l69 z_boson_s68 z_boson_s69) (.seq (.arrow z_boson_l70 z_boson_s69 z_boson_s70) (.seq (.arrow z_boson_l71 z_boson_s70 z_boson_s71) (.seq (.arrow z_boson_l72 z_boson_s71 z_boson_s72) (.seq (.arrow z_boson_l73 z_boson_s72 z_boson_s73) (.seq (.arrow z_boson_l74 z_boson_s73 z_boson_s74) (.seq (.arrow z_boson_l75 z_boson_s74 z_boson_s75) (.seq (.arrow z_boson_l76 z_boson_s75 z_boson_s76) (.seq (.arrow z_boson_l77 z_boson_s76 z_boson_s77) (.seq (.arrow z_boson_l78 z_boson_s77 z_boson_s78) (.seq (.arrow z_boson_l79 z_boson_s78 z_boson_s79) (.seq (.arrow z_boson_l80 z_boson_s79 z_boson_s80) (.seq (.arrow z_boson_l81 z_boson_s80 z_boson_s81) (.seq (.arrow z_boson_l82 z_boson_s81 z_boson_s82) (.seq (.arrow z_boson_l83 z_boson_s82 z_boson_s83) (.seq (.arrow z_boson_l84 z_boson_s83 z_boson_s84) (.seq (.arrow z_boson_l85 z_boson_s84 z_boson_s85) (.seq (.arrow z_boson_l86 z_boson_s85 z_boson_s86) (.seq (.arrow z_boson_l87 z_boson_s86 z_boson_s87) (.seq (.arrow z_boson_l88 z_boson_s87 z_boson_s88) (.seq (.arrow z_boson_l89 z_boson_s88 z_boson_s89) (.seq (.arrow z_boson_l90 z_boson_s89 z_boson_s90) (.seq (.arrow z_boson_l91 z_boson_s90 z_boson_s91) (.seq (.arrow z_boson_l92 z_boson_s91 z_boson_s92) (.seq (.arrow z_boson_l93 z_boson_s92 z_boson_s93) (.seq (.arrow z_boson_l94 z_boson_s93 z_boson_s94) (.seq (.arrow z_boson_l95 z_boson_s94 z_boson_s95) (.seq (.arrow z_boson_l96 z_boson_s95 z_boson_s96) (.seq (.arrow z_boson_l97 z_boson_s96 z_boson_s97) (.seq (.arrow z_boson_l98 z_boson_s97 z_boson_s98) (.seq (.arrow z_boson_l99 z_boson_s98 z_boson_s99) (.seq (.arrow z_boson_l100 z_boson_s99 z_boson_s100) (.arrow z_boson_l101 z_boson_s100 z_boson_s101))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow z_boson_l102 (tensorProduct z_boson_s11 z_boson_s101) z_boson_s102) (.arrow z_boson_l103 z_boson_s102 z_boson_s103))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def z_boson_true_arm : IGProtocol z_boson_initial z_boson_s103 :=
  (z_boson_protocol).restrictToEVALT

-- false arm
noncomputable def z_boson_false_arm : IGProtocol z_boson_initial z_boson_s103 :=
  (z_boson_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def z_boson_tier_ground : OuroboricityTier := TierFunctor.obj z_boson_initial
def z_boson_tier : OuroboricityTier := TierFunctor.obj z_boson_s103
#eval z_boson_tier_ground  -- tier of the ground (pre-transformation)
#eval z_boson_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem z_boson_frobenius :
    igFrobeniusAlg.mul z_boson_initial z_boson_initial = z_boson_initial :=
  igFrobAlg_self_fusion z_boson_initial

theorem z_boson_protocol_depth :
    z_boson_protocol.depth = 97 := by rfl

end Imscribing