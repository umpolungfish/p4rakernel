-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⋈ → ⊤ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊡ → ⋈ → ≺ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⋈ → ⊙ → ⊡ → ⊙ → ⊤ → ≻ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ⊥ → ⋈ → ⊙ → ⊡ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊤ → ⋈ → ⊙ → ⊤ → ≺ → ⊥ → ⋈ → ⊡ → ∋ → ⊣
-- Class: elemental_germanium
-- Fingerprint: sig=(44,2,24,10)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=80
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 78)]

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
--   [24] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [25] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [26] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [27] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [28] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [33] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [34] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [35] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [36] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [37] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [38] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [39] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [40] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [41] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [42] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [43] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [44] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [45] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [46] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [47] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [48] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [49] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [50] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [51] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [52] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [53] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [54] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [55] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [56] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [57] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [58] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [59] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [60] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [61] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [62] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [63] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [64] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [65] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [66] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [67] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [68] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [69] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [70] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [71] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [72] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [73] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [74] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [75] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [76] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [77] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [78] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [79] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def elemental_germanium_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_germanium_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_germanium_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_germanium_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_germanium_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def elemental_germanium_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s58 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s59 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s60 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s61 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s62 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s63 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s64 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s65 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s66 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s67 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s68 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s69 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s70 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s71 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s72 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s73 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s74 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s75 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s76 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s77 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s78 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s79 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def elemental_germanium_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l17 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l25 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l38 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l46 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l53 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l58 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l59 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l60 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l61 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l62 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l63 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l64 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l65 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l66 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l67 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l68 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l69 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l70 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l71 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l72 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l73 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l74 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l75 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l76 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l77 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l78 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l79 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def elemental_germanium_protocol : IGProtocol elemental_germanium_initial elemental_germanium_s79 :=
  .withGram Grammar.measure <|
  (.seq (.arrow elemental_germanium_l0 elemental_germanium_initial elemental_germanium_s0) (.seq (.arrow elemental_germanium_l1 elemental_germanium_s0 elemental_germanium_s1) (.seq (.arrow elemental_germanium_l2 elemental_germanium_s1 elemental_germanium_s2) (.seq (.arrow elemental_germanium_l3 elemental_germanium_s2 elemental_germanium_s3) (.seq (.arrow elemental_germanium_l4 elemental_germanium_s3 elemental_germanium_s4) (.seq (.prod (.seq (.arrow elemental_germanium_l5 elemental_germanium_s4 elemental_germanium_s5) (.seq (.arrow elemental_germanium_l6 elemental_germanium_s5 elemental_germanium_s6) (.seq (.arrow elemental_germanium_l7 elemental_germanium_s6 elemental_germanium_s7) (.seq (.arrow elemental_germanium_l8 elemental_germanium_s7 elemental_germanium_s8) (.seq (.arrow elemental_germanium_l9 elemental_germanium_s8 elemental_germanium_s9) (.seq (.arrow elemental_germanium_l10 elemental_germanium_s9 elemental_germanium_s10) (.seq (.arrow elemental_germanium_l11 elemental_germanium_s10 elemental_germanium_s11) (.seq (.arrow elemental_germanium_l12 elemental_germanium_s11 elemental_germanium_s12) (.arrow elemental_germanium_l13 elemental_germanium_s12 elemental_germanium_s13))))))))) (.seq (.arrow elemental_germanium_l14 elemental_germanium_s4 elemental_germanium_s14) (.seq (.arrow elemental_germanium_l15 elemental_germanium_s14 elemental_germanium_s15) (.seq (.arrow elemental_germanium_l16 elemental_germanium_s15 elemental_germanium_s16) (.seq (.arrow elemental_germanium_l17 elemental_germanium_s16 elemental_germanium_s17) (.seq (.arrow elemental_germanium_l18 elemental_germanium_s17 elemental_germanium_s18) (.seq (.arrow elemental_germanium_l19 elemental_germanium_s18 elemental_germanium_s19) (.seq (.arrow elemental_germanium_l20 elemental_germanium_s19 elemental_germanium_s20) (.seq (.arrow elemental_germanium_l21 elemental_germanium_s20 elemental_germanium_s21) (.seq (.arrow elemental_germanium_l22 elemental_germanium_s21 elemental_germanium_s22) (.seq (.arrow elemental_germanium_l23 elemental_germanium_s22 elemental_germanium_s23) (.seq (.arrow elemental_germanium_l24 elemental_germanium_s23 elemental_germanium_s24) (.seq (.arrow elemental_germanium_l25 elemental_germanium_s24 elemental_germanium_s25) (.seq (.arrow elemental_germanium_l26 elemental_germanium_s25 elemental_germanium_s26) (.seq (.arrow elemental_germanium_l27 elemental_germanium_s26 elemental_germanium_s27) (.seq (.arrow elemental_germanium_l28 elemental_germanium_s27 elemental_germanium_s28) (.seq (.arrow elemental_germanium_l29 elemental_germanium_s28 elemental_germanium_s29) (.seq (.arrow elemental_germanium_l30 elemental_germanium_s29 elemental_germanium_s30) (.seq (.arrow elemental_germanium_l31 elemental_germanium_s30 elemental_germanium_s31) (.seq (.arrow elemental_germanium_l32 elemental_germanium_s31 elemental_germanium_s32) (.seq (.arrow elemental_germanium_l33 elemental_germanium_s32 elemental_germanium_s33) (.seq (.arrow elemental_germanium_l34 elemental_germanium_s33 elemental_germanium_s34) (.seq (.arrow elemental_germanium_l35 elemental_germanium_s34 elemental_germanium_s35) (.seq (.arrow elemental_germanium_l36 elemental_germanium_s35 elemental_germanium_s36) (.seq (.arrow elemental_germanium_l37 elemental_germanium_s36 elemental_germanium_s37) (.seq (.arrow elemental_germanium_l38 elemental_germanium_s37 elemental_germanium_s38) (.seq (.arrow elemental_germanium_l39 elemental_germanium_s38 elemental_germanium_s39) (.seq (.arrow elemental_germanium_l40 elemental_germanium_s39 elemental_germanium_s40) (.seq (.arrow elemental_germanium_l41 elemental_germanium_s40 elemental_germanium_s41) (.seq (.arrow elemental_germanium_l42 elemental_germanium_s41 elemental_germanium_s42) (.seq (.arrow elemental_germanium_l43 elemental_germanium_s42 elemental_germanium_s43) (.seq (.arrow elemental_germanium_l44 elemental_germanium_s43 elemental_germanium_s44) (.seq (.arrow elemental_germanium_l45 elemental_germanium_s44 elemental_germanium_s45) (.seq (.arrow elemental_germanium_l46 elemental_germanium_s45 elemental_germanium_s46) (.seq (.arrow elemental_germanium_l47 elemental_germanium_s46 elemental_germanium_s47) (.seq (.arrow elemental_germanium_l48 elemental_germanium_s47 elemental_germanium_s48) (.seq (.arrow elemental_germanium_l49 elemental_germanium_s48 elemental_germanium_s49) (.seq (.arrow elemental_germanium_l50 elemental_germanium_s49 elemental_germanium_s50) (.seq (.arrow elemental_germanium_l51 elemental_germanium_s50 elemental_germanium_s51) (.seq (.arrow elemental_germanium_l52 elemental_germanium_s51 elemental_germanium_s52) (.seq (.arrow elemental_germanium_l53 elemental_germanium_s52 elemental_germanium_s53) (.seq (.arrow elemental_germanium_l54 elemental_germanium_s53 elemental_germanium_s54) (.seq (.arrow elemental_germanium_l55 elemental_germanium_s54 elemental_germanium_s55) (.seq (.arrow elemental_germanium_l56 elemental_germanium_s55 elemental_germanium_s56) (.seq (.arrow elemental_germanium_l57 elemental_germanium_s56 elemental_germanium_s57) (.seq (.arrow elemental_germanium_l58 elemental_germanium_s57 elemental_germanium_s58) (.seq (.arrow elemental_germanium_l59 elemental_germanium_s58 elemental_germanium_s59) (.seq (.arrow elemental_germanium_l60 elemental_germanium_s59 elemental_germanium_s60) (.seq (.arrow elemental_germanium_l61 elemental_germanium_s60 elemental_germanium_s61) (.seq (.arrow elemental_germanium_l62 elemental_germanium_s61 elemental_germanium_s62) (.seq (.arrow elemental_germanium_l63 elemental_germanium_s62 elemental_germanium_s63) (.seq (.arrow elemental_germanium_l64 elemental_germanium_s63 elemental_germanium_s64) (.seq (.arrow elemental_germanium_l65 elemental_germanium_s64 elemental_germanium_s65) (.seq (.arrow elemental_germanium_l66 elemental_germanium_s65 elemental_germanium_s66) (.seq (.arrow elemental_germanium_l67 elemental_germanium_s66 elemental_germanium_s67) (.seq (.arrow elemental_germanium_l68 elemental_germanium_s67 elemental_germanium_s68) (.seq (.arrow elemental_germanium_l69 elemental_germanium_s68 elemental_germanium_s69) (.seq (.arrow elemental_germanium_l70 elemental_germanium_s69 elemental_germanium_s70) (.seq (.arrow elemental_germanium_l71 elemental_germanium_s70 elemental_germanium_s71) (.seq (.arrow elemental_germanium_l72 elemental_germanium_s71 elemental_germanium_s72) (.seq (.arrow elemental_germanium_l73 elemental_germanium_s72 elemental_germanium_s73) (.seq (.arrow elemental_germanium_l74 elemental_germanium_s73 elemental_germanium_s74) (.seq (.arrow elemental_germanium_l75 elemental_germanium_s74 elemental_germanium_s75) (.seq (.arrow elemental_germanium_l76 elemental_germanium_s75 elemental_germanium_s76) (.arrow elemental_germanium_l77 elemental_germanium_s76 elemental_germanium_s77))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow elemental_germanium_l78 (tensorProduct elemental_germanium_s13 elemental_germanium_s77) elemental_germanium_s78) (.arrow elemental_germanium_l79 elemental_germanium_s78 elemental_germanium_s79))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def elemental_germanium_true_arm : IGProtocol elemental_germanium_initial elemental_germanium_s79 :=
  (elemental_germanium_protocol).restrictToEVALT

-- false arm
noncomputable def elemental_germanium_false_arm : IGProtocol elemental_germanium_initial elemental_germanium_s79 :=
  (elemental_germanium_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def elemental_germanium_tier_ground : OuroboricityTier := TierFunctor.obj elemental_germanium_initial
def elemental_germanium_tier : OuroboricityTier := TierFunctor.obj elemental_germanium_s79
#eval elemental_germanium_tier_ground  -- tier of the ground (pre-transformation)
#eval elemental_germanium_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem elemental_germanium_frobenius :
    igFrobeniusAlg.mul elemental_germanium_initial elemental_germanium_initial = elemental_germanium_initial :=
  igFrobAlg_self_fusion elemental_germanium_initial

theorem elemental_germanium_protocol_depth :
    elemental_germanium_protocol.depth = 71 := by rfl

end Imscribing