-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ≻ → ⊡ → ≺ → ⊞ → ⊙ → ≻ → ⋈ → ⊥ → ⊡ → ⊙ → ≻ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⋈ → ≺ → ⊞ → ⊡ → ⊙ → ⋈ → ≻ → ⊡ → ≺ → ⊥ → ⊡ → ⊞ → ⊙ → ≻ → ≺ → ⊥ → ⋈ → ⊞ → ⊡ → ⊙ → ≻ → ⋈ → ⊙ → ⊡ → ⊙ → ≻ → ⋈ → ⊙ → ⊡ → ∋ → ⊣
-- Class: photon
-- Fingerprint: sig=(34,2,9,9)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=54
-- Expected tier: O₀
-- ∈/∋ pairs: [(4, 52)]

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
--   [5] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [6] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [7] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [8] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [11] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [12] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [13] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [14] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [15] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [19] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [20] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [21] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [25] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [26] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [27] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [28] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [29] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [30] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [31] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [32] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [33] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [34] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [35] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [36] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [37] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [38] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [39] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [40] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [41] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [42] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [43] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [44] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [45] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [46] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [47] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [50] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [51] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [52] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [53] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def photon_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def photon_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def photon_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def photon_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := ah }
private def photon_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def photon_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := hung, prot := ah }
private def photon_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def photon_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def photon_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def photon_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l15 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def photon_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def photon_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def photon_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l29 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def photon_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def photon_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l36 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def photon_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def photon_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l43 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def photon_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def photon_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def photon_protocol : IGProtocol photon_initial photon_s53 :=
  .withGram Grammar.measure <|
  (.seq (.arrow photon_l0 photon_initial photon_s0) (.seq (.arrow photon_l1 photon_s0 photon_s1) (.seq (.arrow photon_l2 photon_s1 photon_s2) (.seq (.arrow photon_l3 photon_s2 photon_s3) (.seq (.arrow photon_l4 photon_s3 photon_s4) (.seq (.prod (.seq (.arrow photon_l5 photon_s4 photon_s5) (.seq (.arrow photon_l6 photon_s5 photon_s6) (.seq (.arrow photon_l7 photon_s6 photon_s7) (.seq (.arrow photon_l8 photon_s7 photon_s8) (.seq (.arrow photon_l9 photon_s8 photon_s9) (.seq (.arrow photon_l10 photon_s9 photon_s10) (.arrow photon_l11 photon_s10 photon_s11))))))) (.seq (.arrow photon_l12 photon_s4 photon_s12) (.seq (.arrow photon_l13 photon_s12 photon_s13) (.seq (.arrow photon_l14 photon_s13 photon_s14) (.seq (.arrow photon_l15 photon_s14 photon_s15) (.seq (.arrow photon_l16 photon_s15 photon_s16) (.seq (.arrow photon_l17 photon_s16 photon_s17) (.seq (.arrow photon_l18 photon_s17 photon_s18) (.seq (.arrow photon_l19 photon_s18 photon_s19) (.seq (.arrow photon_l20 photon_s19 photon_s20) (.seq (.arrow photon_l21 photon_s20 photon_s21) (.seq (.arrow photon_l22 photon_s21 photon_s22) (.seq (.arrow photon_l23 photon_s22 photon_s23) (.seq (.arrow photon_l24 photon_s23 photon_s24) (.seq (.arrow photon_l25 photon_s24 photon_s25) (.seq (.arrow photon_l26 photon_s25 photon_s26) (.seq (.arrow photon_l27 photon_s26 photon_s27) (.seq (.arrow photon_l28 photon_s27 photon_s28) (.seq (.arrow photon_l29 photon_s28 photon_s29) (.seq (.arrow photon_l30 photon_s29 photon_s30) (.seq (.arrow photon_l31 photon_s30 photon_s31) (.seq (.arrow photon_l32 photon_s31 photon_s32) (.seq (.arrow photon_l33 photon_s32 photon_s33) (.seq (.arrow photon_l34 photon_s33 photon_s34) (.seq (.arrow photon_l35 photon_s34 photon_s35) (.seq (.arrow photon_l36 photon_s35 photon_s36) (.seq (.arrow photon_l37 photon_s36 photon_s37) (.seq (.arrow photon_l38 photon_s37 photon_s38) (.seq (.arrow photon_l39 photon_s38 photon_s39) (.seq (.arrow photon_l40 photon_s39 photon_s40) (.seq (.arrow photon_l41 photon_s40 photon_s41) (.seq (.arrow photon_l42 photon_s41 photon_s42) (.seq (.arrow photon_l43 photon_s42 photon_s43) (.seq (.arrow photon_l44 photon_s43 photon_s44) (.seq (.arrow photon_l45 photon_s44 photon_s45) (.seq (.arrow photon_l46 photon_s45 photon_s46) (.seq (.arrow photon_l47 photon_s46 photon_s47) (.seq (.arrow photon_l48 photon_s47 photon_s48) (.seq (.arrow photon_l49 photon_s48 photon_s49) (.seq (.arrow photon_l50 photon_s49 photon_s50) (.arrow photon_l51 photon_s50 photon_s51))))))))))))))))))))))))))))))))))))))))) (.seq (.arrow photon_l52 (tensorProduct photon_s11 photon_s51) photon_s52) (.arrow photon_l53 photon_s52 photon_s53))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- false arm
noncomputable def photon_false_arm : IGProtocol photon_initial photon_s53 :=
  (photon_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₀.
def photon_tier_ground : OuroboricityTier := TierFunctor.obj photon_initial
def photon_tier : OuroboricityTier := TierFunctor.obj photon_s53
#eval photon_tier_ground  -- tier of the ground (pre-transformation)
#eval photon_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem photon_frobenius :
    igFrobeniusAlg.mul photon_initial photon_initial = photon_initial :=
  igFrobAlg_self_fusion photon_initial

theorem photon_protocol_depth :
    photon_protocol.depth = 47 := by rfl

end Imscribing