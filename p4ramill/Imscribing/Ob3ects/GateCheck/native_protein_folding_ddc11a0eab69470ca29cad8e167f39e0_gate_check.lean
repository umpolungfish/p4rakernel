-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ⊤ → ≻ → ⊥ → ≺ → ⊞ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⋈ → ⊡ → ≻ → ⊤ → ⋈ → ⊡ → ⊥ → ≺ → ⊞ → ⊙ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⊥ → ≺ → ⋈ → ⊞ → ⊡ → ≻ → ⊙ → ⊤ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ⊡ → ⋈ → ≻ → ⊤ → ≻ → ⊥ → ≺ → ⊙ → ⋈ → ⊡ → ≻ → ⊤ → ⋈ → ⊤ → ⋈ → ⊡ → ∋ → ⊣
-- Class: native_protein_folding
-- Fingerprint: sig=(40,2,21,11)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=74
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 72)]

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
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [13] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [14] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [15] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [16] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [17] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [18] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [19] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [20] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [21] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [24] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [25] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [26] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [27] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [28] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [31] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [32] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [33] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [34] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [35] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [36] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [37] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [38] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [39] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [40] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [41] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [42] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [43] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [44] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [45] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [46] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [47] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [50] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [51] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [52] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [53] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [55] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [56] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [57] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [58] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [59] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [60] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [61] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [62] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [63] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [64] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [65] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [66] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [67] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [68] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [69] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [70] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [71] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [72] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [73] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def native_protein_folding_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def native_protein_folding_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def native_protein_folding_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def native_protein_folding_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def native_protein_folding_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def native_protein_folding_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def native_protein_folding_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def native_protein_folding_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def native_protein_folding_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l19 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l24 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def native_protein_folding_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l33 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l40 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def native_protein_folding_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def native_protein_folding_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def native_protein_folding_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l58 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l60 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def native_protein_folding_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l66 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def native_protein_folding_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def native_protein_folding_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def native_protein_folding_protocol : IGProtocol native_protein_folding_initial native_protein_folding_s73 :=
  .withGram Grammar.measure <|
  (.seq (.arrow native_protein_folding_l0 native_protein_folding_initial native_protein_folding_s0) (.seq (.arrow native_protein_folding_l1 native_protein_folding_s0 native_protein_folding_s1) (.seq (.arrow native_protein_folding_l2 native_protein_folding_s1 native_protein_folding_s2) (.seq (.arrow native_protein_folding_l3 native_protein_folding_s2 native_protein_folding_s3) (.seq (.arrow native_protein_folding_l4 native_protein_folding_s3 native_protein_folding_s4) (.seq (.prod (.seq (.arrow native_protein_folding_l5 native_protein_folding_s4 native_protein_folding_s5) (.seq (.arrow native_protein_folding_l6 native_protein_folding_s5 native_protein_folding_s6) (.seq (.arrow native_protein_folding_l7 native_protein_folding_s6 native_protein_folding_s7) (.seq (.arrow native_protein_folding_l8 native_protein_folding_s7 native_protein_folding_s8) (.seq (.arrow native_protein_folding_l9 native_protein_folding_s8 native_protein_folding_s9) (.seq (.arrow native_protein_folding_l10 native_protein_folding_s9 native_protein_folding_s10) (.seq (.arrow native_protein_folding_l11 native_protein_folding_s10 native_protein_folding_s11) (.arrow native_protein_folding_l12 native_protein_folding_s11 native_protein_folding_s12)))))))) (.seq (.arrow native_protein_folding_l13 native_protein_folding_s4 native_protein_folding_s13) (.seq (.arrow native_protein_folding_l14 native_protein_folding_s13 native_protein_folding_s14) (.seq (.arrow native_protein_folding_l15 native_protein_folding_s14 native_protein_folding_s15) (.seq (.arrow native_protein_folding_l16 native_protein_folding_s15 native_protein_folding_s16) (.seq (.arrow native_protein_folding_l17 native_protein_folding_s16 native_protein_folding_s17) (.seq (.arrow native_protein_folding_l18 native_protein_folding_s17 native_protein_folding_s18) (.seq (.arrow native_protein_folding_l19 native_protein_folding_s18 native_protein_folding_s19) (.seq (.arrow native_protein_folding_l20 native_protein_folding_s19 native_protein_folding_s20) (.seq (.arrow native_protein_folding_l21 native_protein_folding_s20 native_protein_folding_s21) (.seq (.arrow native_protein_folding_l22 native_protein_folding_s21 native_protein_folding_s22) (.seq (.arrow native_protein_folding_l23 native_protein_folding_s22 native_protein_folding_s23) (.seq (.arrow native_protein_folding_l24 native_protein_folding_s23 native_protein_folding_s24) (.seq (.arrow native_protein_folding_l25 native_protein_folding_s24 native_protein_folding_s25) (.seq (.arrow native_protein_folding_l26 native_protein_folding_s25 native_protein_folding_s26) (.seq (.arrow native_protein_folding_l27 native_protein_folding_s26 native_protein_folding_s27) (.seq (.arrow native_protein_folding_l28 native_protein_folding_s27 native_protein_folding_s28) (.seq (.arrow native_protein_folding_l29 native_protein_folding_s28 native_protein_folding_s29) (.seq (.arrow native_protein_folding_l30 native_protein_folding_s29 native_protein_folding_s30) (.seq (.arrow native_protein_folding_l31 native_protein_folding_s30 native_protein_folding_s31) (.seq (.arrow native_protein_folding_l32 native_protein_folding_s31 native_protein_folding_s32) (.seq (.arrow native_protein_folding_l33 native_protein_folding_s32 native_protein_folding_s33) (.seq (.arrow native_protein_folding_l34 native_protein_folding_s33 native_protein_folding_s34) (.seq (.arrow native_protein_folding_l35 native_protein_folding_s34 native_protein_folding_s35) (.seq (.arrow native_protein_folding_l36 native_protein_folding_s35 native_protein_folding_s36) (.seq (.arrow native_protein_folding_l37 native_protein_folding_s36 native_protein_folding_s37) (.seq (.arrow native_protein_folding_l38 native_protein_folding_s37 native_protein_folding_s38) (.seq (.arrow native_protein_folding_l39 native_protein_folding_s38 native_protein_folding_s39) (.seq (.arrow native_protein_folding_l40 native_protein_folding_s39 native_protein_folding_s40) (.seq (.arrow native_protein_folding_l41 native_protein_folding_s40 native_protein_folding_s41) (.seq (.arrow native_protein_folding_l42 native_protein_folding_s41 native_protein_folding_s42) (.seq (.arrow native_protein_folding_l43 native_protein_folding_s42 native_protein_folding_s43) (.seq (.arrow native_protein_folding_l44 native_protein_folding_s43 native_protein_folding_s44) (.seq (.arrow native_protein_folding_l45 native_protein_folding_s44 native_protein_folding_s45) (.seq (.arrow native_protein_folding_l46 native_protein_folding_s45 native_protein_folding_s46) (.seq (.arrow native_protein_folding_l47 native_protein_folding_s46 native_protein_folding_s47) (.seq (.arrow native_protein_folding_l48 native_protein_folding_s47 native_protein_folding_s48) (.seq (.arrow native_protein_folding_l49 native_protein_folding_s48 native_protein_folding_s49) (.seq (.arrow native_protein_folding_l50 native_protein_folding_s49 native_protein_folding_s50) (.seq (.arrow native_protein_folding_l51 native_protein_folding_s50 native_protein_folding_s51) (.seq (.arrow native_protein_folding_l52 native_protein_folding_s51 native_protein_folding_s52) (.seq (.arrow native_protein_folding_l53 native_protein_folding_s52 native_protein_folding_s53) (.seq (.arrow native_protein_folding_l54 native_protein_folding_s53 native_protein_folding_s54) (.seq (.arrow native_protein_folding_l55 native_protein_folding_s54 native_protein_folding_s55) (.seq (.arrow native_protein_folding_l56 native_protein_folding_s55 native_protein_folding_s56) (.seq (.arrow native_protein_folding_l57 native_protein_folding_s56 native_protein_folding_s57) (.seq (.arrow native_protein_folding_l58 native_protein_folding_s57 native_protein_folding_s58) (.seq (.arrow native_protein_folding_l59 native_protein_folding_s58 native_protein_folding_s59) (.seq (.arrow native_protein_folding_l60 native_protein_folding_s59 native_protein_folding_s60) (.seq (.arrow native_protein_folding_l61 native_protein_folding_s60 native_protein_folding_s61) (.seq (.arrow native_protein_folding_l62 native_protein_folding_s61 native_protein_folding_s62) (.seq (.arrow native_protein_folding_l63 native_protein_folding_s62 native_protein_folding_s63) (.seq (.arrow native_protein_folding_l64 native_protein_folding_s63 native_protein_folding_s64) (.seq (.arrow native_protein_folding_l65 native_protein_folding_s64 native_protein_folding_s65) (.seq (.arrow native_protein_folding_l66 native_protein_folding_s65 native_protein_folding_s66) (.seq (.arrow native_protein_folding_l67 native_protein_folding_s66 native_protein_folding_s67) (.seq (.arrow native_protein_folding_l68 native_protein_folding_s67 native_protein_folding_s68) (.seq (.arrow native_protein_folding_l69 native_protein_folding_s68 native_protein_folding_s69) (.seq (.arrow native_protein_folding_l70 native_protein_folding_s69 native_protein_folding_s70) (.arrow native_protein_folding_l71 native_protein_folding_s70 native_protein_folding_s71)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow native_protein_folding_l72 (tensorProduct native_protein_folding_s12 native_protein_folding_s71) native_protein_folding_s72) (.arrow native_protein_folding_l73 native_protein_folding_s72 native_protein_folding_s73))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def native_protein_folding_true_arm : IGProtocol native_protein_folding_initial native_protein_folding_s73 :=
  (native_protein_folding_protocol).restrictToEVALT

-- false arm
noncomputable def native_protein_folding_false_arm : IGProtocol native_protein_folding_initial native_protein_folding_s73 :=
  (native_protein_folding_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def native_protein_folding_tier_ground : OuroboricityTier := TierFunctor.obj native_protein_folding_initial
def native_protein_folding_tier : OuroboricityTier := TierFunctor.obj native_protein_folding_s73
#eval native_protein_folding_tier_ground  -- tier of the ground (pre-transformation)
#eval native_protein_folding_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem native_protein_folding_frobenius :
    igFrobeniusAlg.mul native_protein_folding_initial native_protein_folding_initial = native_protein_folding_initial :=
  igFrobAlg_self_fusion native_protein_folding_initial

theorem native_protein_folding_protocol_depth :
    native_protein_folding_protocol.depth = 66 := by rfl

end Imscribing