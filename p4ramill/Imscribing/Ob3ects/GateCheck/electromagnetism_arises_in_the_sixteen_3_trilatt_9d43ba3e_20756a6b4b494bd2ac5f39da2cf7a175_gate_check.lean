-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ⊡ → ≻ → ⊤ → ⋈ → ⊥ → ≺ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊡ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ⊤ → ⊡ → ≻ → ⊤ → ⋈ → ∋ → ⊙ → ⊣
-- Class: Electromagnetism_arises_in_the_SIXTEEN_3_trilattice
-- Fingerprint: sig=(38,2,17,10)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=67
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 64)]

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
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [13] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [14] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [15] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [18] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [19] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [20] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [21] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [24] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [25] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [26] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [27] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [28] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [29] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [30] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [31] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [32] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [33] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [34] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [35] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [36] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [37] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [38] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [39] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [40] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [41] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [42] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [43] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [44] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [45] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [46] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [47] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [48] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [49] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [50] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [51] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [52] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [53] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [55] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [56] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [57] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [58] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [59] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [60] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [61] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [62] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [63] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [64] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [65] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [66] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def electromagnetism_arises_in_the_sixteen_b805c3_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def electromagnetism_arises_in_the_sixteen_b805c3_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l27 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l34 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l41 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l45 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l56 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def electromagnetism_arises_in_the_sixteen_b805c3_l61 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def electromagnetism_arises_in_the_sixteen_b805c3_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def electromagnetism_arises_in_the_sixteen_b805c3_protocol : IGProtocol electromagnetism_arises_in_the_sixteen_b805c3_initial electromagnetism_arises_in_the_sixteen_b805c3_s66 :=
  .withGram Grammar.measure <|
  (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l0 electromagnetism_arises_in_the_sixteen_b805c3_initial electromagnetism_arises_in_the_sixteen_b805c3_s0) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l1 electromagnetism_arises_in_the_sixteen_b805c3_s0 electromagnetism_arises_in_the_sixteen_b805c3_s1) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l2 electromagnetism_arises_in_the_sixteen_b805c3_s1 electromagnetism_arises_in_the_sixteen_b805c3_s2) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l3 electromagnetism_arises_in_the_sixteen_b805c3_s2 electromagnetism_arises_in_the_sixteen_b805c3_s3) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l4 electromagnetism_arises_in_the_sixteen_b805c3_s3 electromagnetism_arises_in_the_sixteen_b805c3_s4) (.seq (.prod (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l5 electromagnetism_arises_in_the_sixteen_b805c3_s4 electromagnetism_arises_in_the_sixteen_b805c3_s5) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l6 electromagnetism_arises_in_the_sixteen_b805c3_s5 electromagnetism_arises_in_the_sixteen_b805c3_s6) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l7 electromagnetism_arises_in_the_sixteen_b805c3_s6 electromagnetism_arises_in_the_sixteen_b805c3_s7) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l8 electromagnetism_arises_in_the_sixteen_b805c3_s7 electromagnetism_arises_in_the_sixteen_b805c3_s8) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l9 electromagnetism_arises_in_the_sixteen_b805c3_s8 electromagnetism_arises_in_the_sixteen_b805c3_s9) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l10 electromagnetism_arises_in_the_sixteen_b805c3_s9 electromagnetism_arises_in_the_sixteen_b805c3_s10) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l11 electromagnetism_arises_in_the_sixteen_b805c3_s10 electromagnetism_arises_in_the_sixteen_b805c3_s11) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l12 electromagnetism_arises_in_the_sixteen_b805c3_s11 electromagnetism_arises_in_the_sixteen_b805c3_s12) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l13 electromagnetism_arises_in_the_sixteen_b805c3_s12 electromagnetism_arises_in_the_sixteen_b805c3_s13) (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l14 electromagnetism_arises_in_the_sixteen_b805c3_s13 electromagnetism_arises_in_the_sixteen_b805c3_s14)))))))))) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l15 electromagnetism_arises_in_the_sixteen_b805c3_s4 electromagnetism_arises_in_the_sixteen_b805c3_s15) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l16 electromagnetism_arises_in_the_sixteen_b805c3_s15 electromagnetism_arises_in_the_sixteen_b805c3_s16) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l17 electromagnetism_arises_in_the_sixteen_b805c3_s16 electromagnetism_arises_in_the_sixteen_b805c3_s17) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l18 electromagnetism_arises_in_the_sixteen_b805c3_s17 electromagnetism_arises_in_the_sixteen_b805c3_s18) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l19 electromagnetism_arises_in_the_sixteen_b805c3_s18 electromagnetism_arises_in_the_sixteen_b805c3_s19) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l20 electromagnetism_arises_in_the_sixteen_b805c3_s19 electromagnetism_arises_in_the_sixteen_b805c3_s20) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l21 electromagnetism_arises_in_the_sixteen_b805c3_s20 electromagnetism_arises_in_the_sixteen_b805c3_s21) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l22 electromagnetism_arises_in_the_sixteen_b805c3_s21 electromagnetism_arises_in_the_sixteen_b805c3_s22) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l23 electromagnetism_arises_in_the_sixteen_b805c3_s22 electromagnetism_arises_in_the_sixteen_b805c3_s23) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l24 electromagnetism_arises_in_the_sixteen_b805c3_s23 electromagnetism_arises_in_the_sixteen_b805c3_s24) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l25 electromagnetism_arises_in_the_sixteen_b805c3_s24 electromagnetism_arises_in_the_sixteen_b805c3_s25) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l26 electromagnetism_arises_in_the_sixteen_b805c3_s25 electromagnetism_arises_in_the_sixteen_b805c3_s26) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l27 electromagnetism_arises_in_the_sixteen_b805c3_s26 electromagnetism_arises_in_the_sixteen_b805c3_s27) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l28 electromagnetism_arises_in_the_sixteen_b805c3_s27 electromagnetism_arises_in_the_sixteen_b805c3_s28) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l29 electromagnetism_arises_in_the_sixteen_b805c3_s28 electromagnetism_arises_in_the_sixteen_b805c3_s29) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l30 electromagnetism_arises_in_the_sixteen_b805c3_s29 electromagnetism_arises_in_the_sixteen_b805c3_s30) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l31 electromagnetism_arises_in_the_sixteen_b805c3_s30 electromagnetism_arises_in_the_sixteen_b805c3_s31) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l32 electromagnetism_arises_in_the_sixteen_b805c3_s31 electromagnetism_arises_in_the_sixteen_b805c3_s32) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l33 electromagnetism_arises_in_the_sixteen_b805c3_s32 electromagnetism_arises_in_the_sixteen_b805c3_s33) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l34 electromagnetism_arises_in_the_sixteen_b805c3_s33 electromagnetism_arises_in_the_sixteen_b805c3_s34) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l35 electromagnetism_arises_in_the_sixteen_b805c3_s34 electromagnetism_arises_in_the_sixteen_b805c3_s35) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l36 electromagnetism_arises_in_the_sixteen_b805c3_s35 electromagnetism_arises_in_the_sixteen_b805c3_s36) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l37 electromagnetism_arises_in_the_sixteen_b805c3_s36 electromagnetism_arises_in_the_sixteen_b805c3_s37) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l38 electromagnetism_arises_in_the_sixteen_b805c3_s37 electromagnetism_arises_in_the_sixteen_b805c3_s38) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l39 electromagnetism_arises_in_the_sixteen_b805c3_s38 electromagnetism_arises_in_the_sixteen_b805c3_s39) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l40 electromagnetism_arises_in_the_sixteen_b805c3_s39 electromagnetism_arises_in_the_sixteen_b805c3_s40) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l41 electromagnetism_arises_in_the_sixteen_b805c3_s40 electromagnetism_arises_in_the_sixteen_b805c3_s41) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l42 electromagnetism_arises_in_the_sixteen_b805c3_s41 electromagnetism_arises_in_the_sixteen_b805c3_s42) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l43 electromagnetism_arises_in_the_sixteen_b805c3_s42 electromagnetism_arises_in_the_sixteen_b805c3_s43) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l44 electromagnetism_arises_in_the_sixteen_b805c3_s43 electromagnetism_arises_in_the_sixteen_b805c3_s44) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l45 electromagnetism_arises_in_the_sixteen_b805c3_s44 electromagnetism_arises_in_the_sixteen_b805c3_s45) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l46 electromagnetism_arises_in_the_sixteen_b805c3_s45 electromagnetism_arises_in_the_sixteen_b805c3_s46) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l47 electromagnetism_arises_in_the_sixteen_b805c3_s46 electromagnetism_arises_in_the_sixteen_b805c3_s47) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l48 electromagnetism_arises_in_the_sixteen_b805c3_s47 electromagnetism_arises_in_the_sixteen_b805c3_s48) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l49 electromagnetism_arises_in_the_sixteen_b805c3_s48 electromagnetism_arises_in_the_sixteen_b805c3_s49) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l50 electromagnetism_arises_in_the_sixteen_b805c3_s49 electromagnetism_arises_in_the_sixteen_b805c3_s50) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l51 electromagnetism_arises_in_the_sixteen_b805c3_s50 electromagnetism_arises_in_the_sixteen_b805c3_s51) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l52 electromagnetism_arises_in_the_sixteen_b805c3_s51 electromagnetism_arises_in_the_sixteen_b805c3_s52) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l53 electromagnetism_arises_in_the_sixteen_b805c3_s52 electromagnetism_arises_in_the_sixteen_b805c3_s53) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l54 electromagnetism_arises_in_the_sixteen_b805c3_s53 electromagnetism_arises_in_the_sixteen_b805c3_s54) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l55 electromagnetism_arises_in_the_sixteen_b805c3_s54 electromagnetism_arises_in_the_sixteen_b805c3_s55) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l56 electromagnetism_arises_in_the_sixteen_b805c3_s55 electromagnetism_arises_in_the_sixteen_b805c3_s56) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l57 electromagnetism_arises_in_the_sixteen_b805c3_s56 electromagnetism_arises_in_the_sixteen_b805c3_s57) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l58 electromagnetism_arises_in_the_sixteen_b805c3_s57 electromagnetism_arises_in_the_sixteen_b805c3_s58) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l59 electromagnetism_arises_in_the_sixteen_b805c3_s58 electromagnetism_arises_in_the_sixteen_b805c3_s59) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l60 electromagnetism_arises_in_the_sixteen_b805c3_s59 electromagnetism_arises_in_the_sixteen_b805c3_s60) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l61 electromagnetism_arises_in_the_sixteen_b805c3_s60 electromagnetism_arises_in_the_sixteen_b805c3_s61) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l62 electromagnetism_arises_in_the_sixteen_b805c3_s61 electromagnetism_arises_in_the_sixteen_b805c3_s62) (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l63 electromagnetism_arises_in_the_sixteen_b805c3_s62 electromagnetism_arises_in_the_sixteen_b805c3_s63)))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l64 (tensorProduct electromagnetism_arises_in_the_sixteen_b805c3_s14 electromagnetism_arises_in_the_sixteen_b805c3_s63) electromagnetism_arises_in_the_sixteen_b805c3_s64) (.seq (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l65 electromagnetism_arises_in_the_sixteen_b805c3_s64 electromagnetism_arises_in_the_sixteen_b805c3_s65) (.arrow electromagnetism_arises_in_the_sixteen_b805c3_l66 electromagnetism_arises_in_the_sixteen_b805c3_s65 electromagnetism_arises_in_the_sixteen_b805c3_s66)))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def electromagnetism_arises_in_the_sixteen_b805c3_true_arm : IGProtocol electromagnetism_arises_in_the_sixteen_b805c3_initial electromagnetism_arises_in_the_sixteen_b805c3_s66 :=
  (electromagnetism_arises_in_the_sixteen_b805c3_protocol).restrictToEVALT

-- false arm
noncomputable def electromagnetism_arises_in_the_sixteen_b805c3_false_arm : IGProtocol electromagnetism_arises_in_the_sixteen_b805c3_initial electromagnetism_arises_in_the_sixteen_b805c3_s66 :=
  (electromagnetism_arises_in_the_sixteen_b805c3_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def electromagnetism_arises_in_the_sixteen_b805c3_tier_ground : OuroboricityTier := TierFunctor.obj electromagnetism_arises_in_the_sixteen_b805c3_initial
def electromagnetism_arises_in_the_sixteen_b805c3_tier : OuroboricityTier := TierFunctor.obj electromagnetism_arises_in_the_sixteen_b805c3_s66
#eval electromagnetism_arises_in_the_sixteen_b805c3_tier_ground  -- tier of the ground (pre-transformation)
#eval electromagnetism_arises_in_the_sixteen_b805c3_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem electromagnetism_arises_in_the_sixteen_b805c3_frobenius :
    igFrobeniusAlg.mul electromagnetism_arises_in_the_sixteen_b805c3_initial electromagnetism_arises_in_the_sixteen_b805c3_initial = electromagnetism_arises_in_the_sixteen_b805c3_initial :=
  igFrobAlg_self_fusion electromagnetism_arises_in_the_sixteen_b805c3_initial

theorem electromagnetism_arises_in_the_sixteen_b805c3_protocol_depth :
    electromagnetism_arises_in_the_sixteen_b805c3_protocol.depth = 57 := by rfl

end Imscribing