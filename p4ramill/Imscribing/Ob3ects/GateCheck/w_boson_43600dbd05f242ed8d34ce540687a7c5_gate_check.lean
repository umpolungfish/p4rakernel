-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ∈ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊞ → ≺ → ⊥ → ⊙ → ⊡ → ∋ → ⊣
-- Class: W_boson
-- Fingerprint: sig=(42,2,24,8)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=76
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(3, 74)]

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
--   [3] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [5] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [11] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [12] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [13] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [14] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [15] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [19] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [20] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [21] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [22] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [25] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [26] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [27] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [28] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [29] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [30] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [31] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [32] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [33] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [34] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [35] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [36] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [37] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [38] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [39] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [40] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [41] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [42] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [43] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [44] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [45] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [46] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [47] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [52] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [53] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [54] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [55] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [56] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [57] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [58] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [59] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [60] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [61] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [62] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [63] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [64] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [65] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [66] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [67] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [68] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [69] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [70] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [71] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [72] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [73] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [74] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [75] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def w_boson_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def w_boson_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def w_boson_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def w_boson_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def w_boson_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def w_boson_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def w_boson_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def w_boson_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l30 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l39 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l57 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l66 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def w_boson_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def w_boson_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def w_boson_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def w_boson_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def w_boson_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def w_boson_protocol : IGProtocol w_boson_initial w_boson_s75 :=
  .withGram Grammar.measure <|
  (.seq (.arrow w_boson_l0 w_boson_initial w_boson_s0) (.seq (.arrow w_boson_l1 w_boson_s0 w_boson_s1) (.seq (.arrow w_boson_l2 w_boson_s1 w_boson_s2) (.seq (.arrow w_boson_l3 w_boson_s2 w_boson_s3) (.seq (.prod (.seq (.arrow w_boson_l4 w_boson_s3 w_boson_s4) (.seq (.arrow w_boson_l5 w_boson_s4 w_boson_s5) (.seq (.arrow w_boson_l6 w_boson_s5 w_boson_s6) (.arrow w_boson_l7 w_boson_s6 w_boson_s7)))) (.seq (.arrow w_boson_l8 w_boson_s3 w_boson_s8) (.seq (.arrow w_boson_l9 w_boson_s8 w_boson_s9) (.seq (.arrow w_boson_l10 w_boson_s9 w_boson_s10) (.seq (.arrow w_boson_l11 w_boson_s10 w_boson_s11) (.seq (.arrow w_boson_l12 w_boson_s11 w_boson_s12) (.seq (.arrow w_boson_l13 w_boson_s12 w_boson_s13) (.seq (.arrow w_boson_l14 w_boson_s13 w_boson_s14) (.seq (.arrow w_boson_l15 w_boson_s14 w_boson_s15) (.seq (.arrow w_boson_l16 w_boson_s15 w_boson_s16) (.seq (.arrow w_boson_l17 w_boson_s16 w_boson_s17) (.seq (.arrow w_boson_l18 w_boson_s17 w_boson_s18) (.seq (.arrow w_boson_l19 w_boson_s18 w_boson_s19) (.seq (.arrow w_boson_l20 w_boson_s19 w_boson_s20) (.seq (.arrow w_boson_l21 w_boson_s20 w_boson_s21) (.seq (.arrow w_boson_l22 w_boson_s21 w_boson_s22) (.seq (.arrow w_boson_l23 w_boson_s22 w_boson_s23) (.seq (.arrow w_boson_l24 w_boson_s23 w_boson_s24) (.seq (.arrow w_boson_l25 w_boson_s24 w_boson_s25) (.seq (.arrow w_boson_l26 w_boson_s25 w_boson_s26) (.seq (.arrow w_boson_l27 w_boson_s26 w_boson_s27) (.seq (.arrow w_boson_l28 w_boson_s27 w_boson_s28) (.seq (.arrow w_boson_l29 w_boson_s28 w_boson_s29) (.seq (.arrow w_boson_l30 w_boson_s29 w_boson_s30) (.seq (.arrow w_boson_l31 w_boson_s30 w_boson_s31) (.seq (.arrow w_boson_l32 w_boson_s31 w_boson_s32) (.seq (.arrow w_boson_l33 w_boson_s32 w_boson_s33) (.seq (.arrow w_boson_l34 w_boson_s33 w_boson_s34) (.seq (.arrow w_boson_l35 w_boson_s34 w_boson_s35) (.seq (.arrow w_boson_l36 w_boson_s35 w_boson_s36) (.seq (.arrow w_boson_l37 w_boson_s36 w_boson_s37) (.seq (.arrow w_boson_l38 w_boson_s37 w_boson_s38) (.seq (.arrow w_boson_l39 w_boson_s38 w_boson_s39) (.seq (.arrow w_boson_l40 w_boson_s39 w_boson_s40) (.seq (.arrow w_boson_l41 w_boson_s40 w_boson_s41) (.seq (.arrow w_boson_l42 w_boson_s41 w_boson_s42) (.seq (.arrow w_boson_l43 w_boson_s42 w_boson_s43) (.seq (.arrow w_boson_l44 w_boson_s43 w_boson_s44) (.seq (.arrow w_boson_l45 w_boson_s44 w_boson_s45) (.seq (.arrow w_boson_l46 w_boson_s45 w_boson_s46) (.seq (.arrow w_boson_l47 w_boson_s46 w_boson_s47) (.seq (.arrow w_boson_l48 w_boson_s47 w_boson_s48) (.seq (.arrow w_boson_l49 w_boson_s48 w_boson_s49) (.seq (.arrow w_boson_l50 w_boson_s49 w_boson_s50) (.seq (.arrow w_boson_l51 w_boson_s50 w_boson_s51) (.seq (.arrow w_boson_l52 w_boson_s51 w_boson_s52) (.seq (.arrow w_boson_l53 w_boson_s52 w_boson_s53) (.seq (.arrow w_boson_l54 w_boson_s53 w_boson_s54) (.seq (.arrow w_boson_l55 w_boson_s54 w_boson_s55) (.seq (.arrow w_boson_l56 w_boson_s55 w_boson_s56) (.seq (.arrow w_boson_l57 w_boson_s56 w_boson_s57) (.seq (.arrow w_boson_l58 w_boson_s57 w_boson_s58) (.seq (.arrow w_boson_l59 w_boson_s58 w_boson_s59) (.seq (.arrow w_boson_l60 w_boson_s59 w_boson_s60) (.seq (.arrow w_boson_l61 w_boson_s60 w_boson_s61) (.seq (.arrow w_boson_l62 w_boson_s61 w_boson_s62) (.seq (.arrow w_boson_l63 w_boson_s62 w_boson_s63) (.seq (.arrow w_boson_l64 w_boson_s63 w_boson_s64) (.seq (.arrow w_boson_l65 w_boson_s64 w_boson_s65) (.seq (.arrow w_boson_l66 w_boson_s65 w_boson_s66) (.seq (.arrow w_boson_l67 w_boson_s66 w_boson_s67) (.seq (.arrow w_boson_l68 w_boson_s67 w_boson_s68) (.seq (.arrow w_boson_l69 w_boson_s68 w_boson_s69) (.seq (.arrow w_boson_l70 w_boson_s69 w_boson_s70) (.seq (.arrow w_boson_l71 w_boson_s70 w_boson_s71) (.seq (.arrow w_boson_l72 w_boson_s71 w_boson_s72) (.arrow w_boson_l73 w_boson_s72 w_boson_s73))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow w_boson_l74 (tensorProduct w_boson_s7 w_boson_s73) w_boson_s74) (.arrow w_boson_l75 w_boson_s74 w_boson_s75)))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def w_boson_true_arm : IGProtocol w_boson_initial w_boson_s75 :=
  (w_boson_protocol).restrictToEVALT

-- false arm
noncomputable def w_boson_false_arm : IGProtocol w_boson_initial w_boson_s75 :=
  (w_boson_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def w_boson_tier_ground : OuroboricityTier := TierFunctor.obj w_boson_initial
def w_boson_tier : OuroboricityTier := TierFunctor.obj w_boson_s75
#eval w_boson_tier_ground  -- tier of the ground (pre-transformation)
#eval w_boson_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem w_boson_frobenius :
    igFrobeniusAlg.mul w_boson_initial w_boson_initial = w_boson_initial :=
  igFrobAlg_self_fusion w_boson_initial

theorem w_boson_protocol_depth :
    w_boson_protocol.depth = 72 := by rfl

end Imscribing