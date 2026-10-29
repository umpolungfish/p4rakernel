-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ⊡ → ≻ → ⊤ → ≺ → ⋈ → ⊙ → ≻ → ⊤ → ≺ → ⋈ → ⊡ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ∋ → ⊣
-- Class: exact_native_protein_folding_law
-- Fingerprint: sig=(43,2,18,10)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=73
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 71)]

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
--   [14] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [15] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [16] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [17] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [18] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [19] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [20] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [21] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [24] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [27] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [28] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [29] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [30] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [33] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [34] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [35] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [36] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [37] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [38] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [39] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [40] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [41] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [42] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [43] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [44] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [45] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [46] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [47] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [48] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [49] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [50] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [51] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [52] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [53] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [54] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [55] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [56] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [57] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [58] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [59] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [60] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [61] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [62] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [63] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [64] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [65] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [66] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [67] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [68] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [69] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [70] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [71] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [72] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def exact_native_protein_folding_law_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def exact_native_protein_folding_law_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def exact_native_protein_folding_law_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l17 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l24 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l29 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l36 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l38 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l43 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l45 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l50 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l52 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l57 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l59 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l64 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l66 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l67 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def exact_native_protein_folding_law_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def exact_native_protein_folding_law_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def exact_native_protein_folding_law_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def exact_native_protein_folding_law_protocol : IGProtocol exact_native_protein_folding_law_initial exact_native_protein_folding_law_s72 :=
  .withGram Grammar.measure <|
  (.seq (.arrow exact_native_protein_folding_law_l0 exact_native_protein_folding_law_initial exact_native_protein_folding_law_s0) (.seq (.arrow exact_native_protein_folding_law_l1 exact_native_protein_folding_law_s0 exact_native_protein_folding_law_s1) (.seq (.arrow exact_native_protein_folding_law_l2 exact_native_protein_folding_law_s1 exact_native_protein_folding_law_s2) (.seq (.arrow exact_native_protein_folding_law_l3 exact_native_protein_folding_law_s2 exact_native_protein_folding_law_s3) (.seq (.arrow exact_native_protein_folding_law_l4 exact_native_protein_folding_law_s3 exact_native_protein_folding_law_s4) (.seq (.prod (.seq (.arrow exact_native_protein_folding_law_l5 exact_native_protein_folding_law_s4 exact_native_protein_folding_law_s5) (.seq (.arrow exact_native_protein_folding_law_l6 exact_native_protein_folding_law_s5 exact_native_protein_folding_law_s6) (.arrow exact_native_protein_folding_law_l7 exact_native_protein_folding_law_s6 exact_native_protein_folding_law_s7))) (.seq (.arrow exact_native_protein_folding_law_l8 exact_native_protein_folding_law_s4 exact_native_protein_folding_law_s8) (.seq (.arrow exact_native_protein_folding_law_l9 exact_native_protein_folding_law_s8 exact_native_protein_folding_law_s9) (.seq (.arrow exact_native_protein_folding_law_l10 exact_native_protein_folding_law_s9 exact_native_protein_folding_law_s10) (.seq (.arrow exact_native_protein_folding_law_l11 exact_native_protein_folding_law_s10 exact_native_protein_folding_law_s11) (.seq (.arrow exact_native_protein_folding_law_l12 exact_native_protein_folding_law_s11 exact_native_protein_folding_law_s12) (.seq (.arrow exact_native_protein_folding_law_l13 exact_native_protein_folding_law_s12 exact_native_protein_folding_law_s13) (.seq (.arrow exact_native_protein_folding_law_l14 exact_native_protein_folding_law_s13 exact_native_protein_folding_law_s14) (.seq (.arrow exact_native_protein_folding_law_l15 exact_native_protein_folding_law_s14 exact_native_protein_folding_law_s15) (.seq (.arrow exact_native_protein_folding_law_l16 exact_native_protein_folding_law_s15 exact_native_protein_folding_law_s16) (.seq (.arrow exact_native_protein_folding_law_l17 exact_native_protein_folding_law_s16 exact_native_protein_folding_law_s17) (.seq (.arrow exact_native_protein_folding_law_l18 exact_native_protein_folding_law_s17 exact_native_protein_folding_law_s18) (.seq (.arrow exact_native_protein_folding_law_l19 exact_native_protein_folding_law_s18 exact_native_protein_folding_law_s19) (.seq (.arrow exact_native_protein_folding_law_l20 exact_native_protein_folding_law_s19 exact_native_protein_folding_law_s20) (.seq (.arrow exact_native_protein_folding_law_l21 exact_native_protein_folding_law_s20 exact_native_protein_folding_law_s21) (.seq (.arrow exact_native_protein_folding_law_l22 exact_native_protein_folding_law_s21 exact_native_protein_folding_law_s22) (.seq (.arrow exact_native_protein_folding_law_l23 exact_native_protein_folding_law_s22 exact_native_protein_folding_law_s23) (.seq (.arrow exact_native_protein_folding_law_l24 exact_native_protein_folding_law_s23 exact_native_protein_folding_law_s24) (.seq (.arrow exact_native_protein_folding_law_l25 exact_native_protein_folding_law_s24 exact_native_protein_folding_law_s25) (.seq (.arrow exact_native_protein_folding_law_l26 exact_native_protein_folding_law_s25 exact_native_protein_folding_law_s26) (.seq (.arrow exact_native_protein_folding_law_l27 exact_native_protein_folding_law_s26 exact_native_protein_folding_law_s27) (.seq (.arrow exact_native_protein_folding_law_l28 exact_native_protein_folding_law_s27 exact_native_protein_folding_law_s28) (.seq (.arrow exact_native_protein_folding_law_l29 exact_native_protein_folding_law_s28 exact_native_protein_folding_law_s29) (.seq (.arrow exact_native_protein_folding_law_l30 exact_native_protein_folding_law_s29 exact_native_protein_folding_law_s30) (.seq (.arrow exact_native_protein_folding_law_l31 exact_native_protein_folding_law_s30 exact_native_protein_folding_law_s31) (.seq (.arrow exact_native_protein_folding_law_l32 exact_native_protein_folding_law_s31 exact_native_protein_folding_law_s32) (.seq (.arrow exact_native_protein_folding_law_l33 exact_native_protein_folding_law_s32 exact_native_protein_folding_law_s33) (.seq (.arrow exact_native_protein_folding_law_l34 exact_native_protein_folding_law_s33 exact_native_protein_folding_law_s34) (.seq (.arrow exact_native_protein_folding_law_l35 exact_native_protein_folding_law_s34 exact_native_protein_folding_law_s35) (.seq (.arrow exact_native_protein_folding_law_l36 exact_native_protein_folding_law_s35 exact_native_protein_folding_law_s36) (.seq (.arrow exact_native_protein_folding_law_l37 exact_native_protein_folding_law_s36 exact_native_protein_folding_law_s37) (.seq (.arrow exact_native_protein_folding_law_l38 exact_native_protein_folding_law_s37 exact_native_protein_folding_law_s38) (.seq (.arrow exact_native_protein_folding_law_l39 exact_native_protein_folding_law_s38 exact_native_protein_folding_law_s39) (.seq (.arrow exact_native_protein_folding_law_l40 exact_native_protein_folding_law_s39 exact_native_protein_folding_law_s40) (.seq (.arrow exact_native_protein_folding_law_l41 exact_native_protein_folding_law_s40 exact_native_protein_folding_law_s41) (.seq (.arrow exact_native_protein_folding_law_l42 exact_native_protein_folding_law_s41 exact_native_protein_folding_law_s42) (.seq (.arrow exact_native_protein_folding_law_l43 exact_native_protein_folding_law_s42 exact_native_protein_folding_law_s43) (.seq (.arrow exact_native_protein_folding_law_l44 exact_native_protein_folding_law_s43 exact_native_protein_folding_law_s44) (.seq (.arrow exact_native_protein_folding_law_l45 exact_native_protein_folding_law_s44 exact_native_protein_folding_law_s45) (.seq (.arrow exact_native_protein_folding_law_l46 exact_native_protein_folding_law_s45 exact_native_protein_folding_law_s46) (.seq (.arrow exact_native_protein_folding_law_l47 exact_native_protein_folding_law_s46 exact_native_protein_folding_law_s47) (.seq (.arrow exact_native_protein_folding_law_l48 exact_native_protein_folding_law_s47 exact_native_protein_folding_law_s48) (.seq (.arrow exact_native_protein_folding_law_l49 exact_native_protein_folding_law_s48 exact_native_protein_folding_law_s49) (.seq (.arrow exact_native_protein_folding_law_l50 exact_native_protein_folding_law_s49 exact_native_protein_folding_law_s50) (.seq (.arrow exact_native_protein_folding_law_l51 exact_native_protein_folding_law_s50 exact_native_protein_folding_law_s51) (.seq (.arrow exact_native_protein_folding_law_l52 exact_native_protein_folding_law_s51 exact_native_protein_folding_law_s52) (.seq (.arrow exact_native_protein_folding_law_l53 exact_native_protein_folding_law_s52 exact_native_protein_folding_law_s53) (.seq (.arrow exact_native_protein_folding_law_l54 exact_native_protein_folding_law_s53 exact_native_protein_folding_law_s54) (.seq (.arrow exact_native_protein_folding_law_l55 exact_native_protein_folding_law_s54 exact_native_protein_folding_law_s55) (.seq (.arrow exact_native_protein_folding_law_l56 exact_native_protein_folding_law_s55 exact_native_protein_folding_law_s56) (.seq (.arrow exact_native_protein_folding_law_l57 exact_native_protein_folding_law_s56 exact_native_protein_folding_law_s57) (.seq (.arrow exact_native_protein_folding_law_l58 exact_native_protein_folding_law_s57 exact_native_protein_folding_law_s58) (.seq (.arrow exact_native_protein_folding_law_l59 exact_native_protein_folding_law_s58 exact_native_protein_folding_law_s59) (.seq (.arrow exact_native_protein_folding_law_l60 exact_native_protein_folding_law_s59 exact_native_protein_folding_law_s60) (.seq (.arrow exact_native_protein_folding_law_l61 exact_native_protein_folding_law_s60 exact_native_protein_folding_law_s61) (.seq (.arrow exact_native_protein_folding_law_l62 exact_native_protein_folding_law_s61 exact_native_protein_folding_law_s62) (.seq (.arrow exact_native_protein_folding_law_l63 exact_native_protein_folding_law_s62 exact_native_protein_folding_law_s63) (.seq (.arrow exact_native_protein_folding_law_l64 exact_native_protein_folding_law_s63 exact_native_protein_folding_law_s64) (.seq (.arrow exact_native_protein_folding_law_l65 exact_native_protein_folding_law_s64 exact_native_protein_folding_law_s65) (.seq (.arrow exact_native_protein_folding_law_l66 exact_native_protein_folding_law_s65 exact_native_protein_folding_law_s66) (.seq (.arrow exact_native_protein_folding_law_l67 exact_native_protein_folding_law_s66 exact_native_protein_folding_law_s67) (.seq (.arrow exact_native_protein_folding_law_l68 exact_native_protein_folding_law_s67 exact_native_protein_folding_law_s68) (.seq (.arrow exact_native_protein_folding_law_l69 exact_native_protein_folding_law_s68 exact_native_protein_folding_law_s69) (.arrow exact_native_protein_folding_law_l70 exact_native_protein_folding_law_s69 exact_native_protein_folding_law_s70)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow exact_native_protein_folding_law_l71 (tensorProduct exact_native_protein_folding_law_s7 exact_native_protein_folding_law_s70) exact_native_protein_folding_law_s71) (.arrow exact_native_protein_folding_law_l72 exact_native_protein_folding_law_s71 exact_native_protein_folding_law_s72))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def exact_native_protein_folding_law_true_arm : IGProtocol exact_native_protein_folding_law_initial exact_native_protein_folding_law_s72 :=
  (exact_native_protein_folding_law_protocol).restrictToEVALT

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def exact_native_protein_folding_law_tier_ground : OuroboricityTier := TierFunctor.obj exact_native_protein_folding_law_initial
def exact_native_protein_folding_law_tier : OuroboricityTier := TierFunctor.obj exact_native_protein_folding_law_s72
#eval exact_native_protein_folding_law_tier_ground  -- tier of the ground (pre-transformation)
#eval exact_native_protein_folding_law_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem exact_native_protein_folding_law_frobenius :
    igFrobeniusAlg.mul exact_native_protein_folding_law_initial exact_native_protein_folding_law_initial = exact_native_protein_folding_law_initial :=
  igFrobAlg_self_fusion exact_native_protein_folding_law_initial

theorem exact_native_protein_folding_law_protocol_depth :
    exact_native_protein_folding_law_protocol.depth = 70 := by rfl

end Imscribing