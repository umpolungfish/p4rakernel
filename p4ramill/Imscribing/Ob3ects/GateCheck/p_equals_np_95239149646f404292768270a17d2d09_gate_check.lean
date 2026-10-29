-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊡ → ≺ → ⊥ → ⊙ → ⊙ → ≻ → ⋈ → ⊤ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊤ → ≻ → ≺ → ⋈ → ⊙ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ⊥ → ⋈ → ⊙ → ⊡ → ⊙ → ⊡ → ⋈ → ≻ → ⊤ → ≻ → ⊥ → ≺ → ⊙ → ⋈ → ⊡ → ≻ → ⊤ → ⊙ → ⋈ → ⊡ → ≻ → ⊤ → ⋈ → ⊤ → ⋈ → ⊡ → ∋ → ⊣
-- Class: P_equals_NP
-- Fingerprint: sig=(43,2,20,11)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=76
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 74)]

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
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
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
--   [24] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [25] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [26] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [27] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [28] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [29] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [30] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [31] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [32] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [33] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [34] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [35] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [36] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [37] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [38] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [39] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [40] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [41] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [42] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [43] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [44] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [45] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [46] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [47] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [48] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [49] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [50] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [51] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [52] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [53] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [54] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [55] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [56] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [57] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [58] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [59] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [60] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [61] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [62] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [63] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [64] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [65] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [66] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [67] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [68] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [69] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [70] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [71] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [72] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [73] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [74] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [75] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def p_equals_np_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def p_equals_np_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def p_equals_np_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def p_equals_np_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def p_equals_np_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def p_equals_np_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l17 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def p_equals_np_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def p_equals_np_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l25 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def p_equals_np_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l32 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def p_equals_np_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l39 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def p_equals_np_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l46 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def p_equals_np_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l55 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l57 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def p_equals_np_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l63 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l68 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def p_equals_np_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def p_equals_np_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def p_equals_np_protocol : IGProtocol p_equals_np_initial p_equals_np_s75 :=
  .withGram Grammar.measure <|
  (.seq (.arrow p_equals_np_l0 p_equals_np_initial p_equals_np_s0) (.seq (.arrow p_equals_np_l1 p_equals_np_s0 p_equals_np_s1) (.seq (.arrow p_equals_np_l2 p_equals_np_s1 p_equals_np_s2) (.seq (.prod (.seq (.arrow p_equals_np_l3 p_equals_np_s2 p_equals_np_s3) (.seq (.arrow p_equals_np_l4 p_equals_np_s3 p_equals_np_s4) (.seq (.arrow p_equals_np_l5 p_equals_np_s4 p_equals_np_s5) (.seq (.arrow p_equals_np_l6 p_equals_np_s5 p_equals_np_s6) (.arrow p_equals_np_l7 p_equals_np_s6 p_equals_np_s7))))) (.seq (.arrow p_equals_np_l8 p_equals_np_s2 p_equals_np_s8) (.seq (.arrow p_equals_np_l9 p_equals_np_s8 p_equals_np_s9) (.seq (.arrow p_equals_np_l10 p_equals_np_s9 p_equals_np_s10) (.seq (.arrow p_equals_np_l11 p_equals_np_s10 p_equals_np_s11) (.seq (.arrow p_equals_np_l12 p_equals_np_s11 p_equals_np_s12) (.seq (.arrow p_equals_np_l13 p_equals_np_s12 p_equals_np_s13) (.seq (.arrow p_equals_np_l14 p_equals_np_s13 p_equals_np_s14) (.seq (.arrow p_equals_np_l15 p_equals_np_s14 p_equals_np_s15) (.seq (.arrow p_equals_np_l16 p_equals_np_s15 p_equals_np_s16) (.seq (.arrow p_equals_np_l17 p_equals_np_s16 p_equals_np_s17) (.seq (.arrow p_equals_np_l18 p_equals_np_s17 p_equals_np_s18) (.seq (.arrow p_equals_np_l19 p_equals_np_s18 p_equals_np_s19) (.seq (.arrow p_equals_np_l20 p_equals_np_s19 p_equals_np_s20) (.seq (.arrow p_equals_np_l21 p_equals_np_s20 p_equals_np_s21) (.seq (.arrow p_equals_np_l22 p_equals_np_s21 p_equals_np_s22) (.seq (.arrow p_equals_np_l23 p_equals_np_s22 p_equals_np_s23) (.seq (.arrow p_equals_np_l24 p_equals_np_s23 p_equals_np_s24) (.seq (.arrow p_equals_np_l25 p_equals_np_s24 p_equals_np_s25) (.seq (.arrow p_equals_np_l26 p_equals_np_s25 p_equals_np_s26) (.seq (.arrow p_equals_np_l27 p_equals_np_s26 p_equals_np_s27) (.seq (.arrow p_equals_np_l28 p_equals_np_s27 p_equals_np_s28) (.seq (.arrow p_equals_np_l29 p_equals_np_s28 p_equals_np_s29) (.seq (.arrow p_equals_np_l30 p_equals_np_s29 p_equals_np_s30) (.seq (.arrow p_equals_np_l31 p_equals_np_s30 p_equals_np_s31) (.seq (.arrow p_equals_np_l32 p_equals_np_s31 p_equals_np_s32) (.seq (.arrow p_equals_np_l33 p_equals_np_s32 p_equals_np_s33) (.seq (.arrow p_equals_np_l34 p_equals_np_s33 p_equals_np_s34) (.seq (.arrow p_equals_np_l35 p_equals_np_s34 p_equals_np_s35) (.seq (.arrow p_equals_np_l36 p_equals_np_s35 p_equals_np_s36) (.seq (.arrow p_equals_np_l37 p_equals_np_s36 p_equals_np_s37) (.seq (.arrow p_equals_np_l38 p_equals_np_s37 p_equals_np_s38) (.seq (.arrow p_equals_np_l39 p_equals_np_s38 p_equals_np_s39) (.seq (.arrow p_equals_np_l40 p_equals_np_s39 p_equals_np_s40) (.seq (.arrow p_equals_np_l41 p_equals_np_s40 p_equals_np_s41) (.seq (.arrow p_equals_np_l42 p_equals_np_s41 p_equals_np_s42) (.seq (.arrow p_equals_np_l43 p_equals_np_s42 p_equals_np_s43) (.seq (.arrow p_equals_np_l44 p_equals_np_s43 p_equals_np_s44) (.seq (.arrow p_equals_np_l45 p_equals_np_s44 p_equals_np_s45) (.seq (.arrow p_equals_np_l46 p_equals_np_s45 p_equals_np_s46) (.seq (.arrow p_equals_np_l47 p_equals_np_s46 p_equals_np_s47) (.seq (.arrow p_equals_np_l48 p_equals_np_s47 p_equals_np_s48) (.seq (.arrow p_equals_np_l49 p_equals_np_s48 p_equals_np_s49) (.seq (.arrow p_equals_np_l50 p_equals_np_s49 p_equals_np_s50) (.seq (.arrow p_equals_np_l51 p_equals_np_s50 p_equals_np_s51) (.seq (.arrow p_equals_np_l52 p_equals_np_s51 p_equals_np_s52) (.seq (.arrow p_equals_np_l53 p_equals_np_s52 p_equals_np_s53) (.seq (.arrow p_equals_np_l54 p_equals_np_s53 p_equals_np_s54) (.seq (.arrow p_equals_np_l55 p_equals_np_s54 p_equals_np_s55) (.seq (.arrow p_equals_np_l56 p_equals_np_s55 p_equals_np_s56) (.seq (.arrow p_equals_np_l57 p_equals_np_s56 p_equals_np_s57) (.seq (.arrow p_equals_np_l58 p_equals_np_s57 p_equals_np_s58) (.seq (.arrow p_equals_np_l59 p_equals_np_s58 p_equals_np_s59) (.seq (.arrow p_equals_np_l60 p_equals_np_s59 p_equals_np_s60) (.seq (.arrow p_equals_np_l61 p_equals_np_s60 p_equals_np_s61) (.seq (.arrow p_equals_np_l62 p_equals_np_s61 p_equals_np_s62) (.seq (.arrow p_equals_np_l63 p_equals_np_s62 p_equals_np_s63) (.seq (.arrow p_equals_np_l64 p_equals_np_s63 p_equals_np_s64) (.seq (.arrow p_equals_np_l65 p_equals_np_s64 p_equals_np_s65) (.seq (.arrow p_equals_np_l66 p_equals_np_s65 p_equals_np_s66) (.seq (.arrow p_equals_np_l67 p_equals_np_s66 p_equals_np_s67) (.seq (.arrow p_equals_np_l68 p_equals_np_s67 p_equals_np_s68) (.seq (.arrow p_equals_np_l69 p_equals_np_s68 p_equals_np_s69) (.seq (.arrow p_equals_np_l70 p_equals_np_s69 p_equals_np_s70) (.seq (.arrow p_equals_np_l71 p_equals_np_s70 p_equals_np_s71) (.seq (.arrow p_equals_np_l72 p_equals_np_s71 p_equals_np_s72) (.arrow p_equals_np_l73 p_equals_np_s72 p_equals_np_s73))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow p_equals_np_l74 (tensorProduct p_equals_np_s7 p_equals_np_s73) p_equals_np_s74) (.arrow p_equals_np_l75 p_equals_np_s74 p_equals_np_s75))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def p_equals_np_true_arm : IGProtocol p_equals_np_initial p_equals_np_s75 :=
  (p_equals_np_protocol).restrictToEVALT

-- false arm
noncomputable def p_equals_np_false_arm : IGProtocol p_equals_np_initial p_equals_np_s75 :=
  (p_equals_np_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def p_equals_np_tier_ground : OuroboricityTier := TierFunctor.obj p_equals_np_initial
def p_equals_np_tier : OuroboricityTier := TierFunctor.obj p_equals_np_s75
#eval p_equals_np_tier_ground  -- tier of the ground (pre-transformation)
#eval p_equals_np_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem p_equals_np_frobenius :
    igFrobeniusAlg.mul p_equals_np_initial p_equals_np_initial = p_equals_np_initial :=
  igFrobAlg_self_fusion p_equals_np_initial

theorem p_equals_np_protocol_depth :
    p_equals_np_protocol.depth = 71 := by rfl

end Imscribing