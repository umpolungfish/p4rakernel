-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊡ → ≺ → ⊞ → ⊙ → ⊙ → ⊤ → ≻ → ⊞ → ≺ → ⊥ → ⋈ → ⊡ → ⊙ → ≻ → ⊤ → ≺ → ⊞ → ⋈ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ⋈ → ≺ → ⊥ → ⊡ → ⊙ → ≻ → ⊤ → ⊞ → ⋈ → ⊙ → ⊡ → ⊙ → ⊡ → ⋈ → ≻ → ⊤ → ≻ → ⊞ → ≺ → ⊙ → ⋈ → ⊙ → ⊡ → ∋ → ⊣
-- Class: trapping_semiprime_factors_using_braiding_and_spindle_mechanics
-- Fingerprint: sig=(31,2,14,7)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=54
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 52)]

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
--   [8] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [9] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [12] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [13] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [14] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [15] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [16] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [17] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [18] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [19] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [20] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [21] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [22] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [27] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [28] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [29] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [30] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [31] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [32] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [33] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [34] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [35] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [36] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [37] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [38] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [39] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [40] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [41] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [42] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [43] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [44] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [45] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [46] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [47] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [48] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [49] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [50] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [51] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [52] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [53] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def trapping_semiprime_factors_using_dc1319_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def trapping_semiprime_factors_using_dc1319_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l12 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l19 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l27 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l34 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l43 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l45 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def trapping_semiprime_factors_using_dc1319_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def trapping_semiprime_factors_using_dc1319_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def trapping_semiprime_factors_using_dc1319_protocol : IGProtocol trapping_semiprime_factors_using_dc1319_initial trapping_semiprime_factors_using_dc1319_s53 :=
  .withGram Grammar.measure <|
  (.seq (.arrow trapping_semiprime_factors_using_dc1319_l0 trapping_semiprime_factors_using_dc1319_initial trapping_semiprime_factors_using_dc1319_s0) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l1 trapping_semiprime_factors_using_dc1319_s0 trapping_semiprime_factors_using_dc1319_s1) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l2 trapping_semiprime_factors_using_dc1319_s1 trapping_semiprime_factors_using_dc1319_s2) (.seq (.prod (.seq (.arrow trapping_semiprime_factors_using_dc1319_l3 trapping_semiprime_factors_using_dc1319_s2 trapping_semiprime_factors_using_dc1319_s3) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l4 trapping_semiprime_factors_using_dc1319_s3 trapping_semiprime_factors_using_dc1319_s4) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l5 trapping_semiprime_factors_using_dc1319_s4 trapping_semiprime_factors_using_dc1319_s5) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l6 trapping_semiprime_factors_using_dc1319_s5 trapping_semiprime_factors_using_dc1319_s6) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l7 trapping_semiprime_factors_using_dc1319_s6 trapping_semiprime_factors_using_dc1319_s7) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l8 trapping_semiprime_factors_using_dc1319_s7 trapping_semiprime_factors_using_dc1319_s8) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l9 trapping_semiprime_factors_using_dc1319_s8 trapping_semiprime_factors_using_dc1319_s9) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l10 trapping_semiprime_factors_using_dc1319_s9 trapping_semiprime_factors_using_dc1319_s10) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l11 trapping_semiprime_factors_using_dc1319_s10 trapping_semiprime_factors_using_dc1319_s11) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l12 trapping_semiprime_factors_using_dc1319_s11 trapping_semiprime_factors_using_dc1319_s12) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l13 trapping_semiprime_factors_using_dc1319_s12 trapping_semiprime_factors_using_dc1319_s13) (.arrow trapping_semiprime_factors_using_dc1319_l14 trapping_semiprime_factors_using_dc1319_s13 trapping_semiprime_factors_using_dc1319_s14)))))))))))) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l15 trapping_semiprime_factors_using_dc1319_s2 trapping_semiprime_factors_using_dc1319_s15) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l16 trapping_semiprime_factors_using_dc1319_s15 trapping_semiprime_factors_using_dc1319_s16) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l17 trapping_semiprime_factors_using_dc1319_s16 trapping_semiprime_factors_using_dc1319_s17) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l18 trapping_semiprime_factors_using_dc1319_s17 trapping_semiprime_factors_using_dc1319_s18) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l19 trapping_semiprime_factors_using_dc1319_s18 trapping_semiprime_factors_using_dc1319_s19) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l20 trapping_semiprime_factors_using_dc1319_s19 trapping_semiprime_factors_using_dc1319_s20) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l21 trapping_semiprime_factors_using_dc1319_s20 trapping_semiprime_factors_using_dc1319_s21) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l22 trapping_semiprime_factors_using_dc1319_s21 trapping_semiprime_factors_using_dc1319_s22) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l23 trapping_semiprime_factors_using_dc1319_s22 trapping_semiprime_factors_using_dc1319_s23) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l24 trapping_semiprime_factors_using_dc1319_s23 trapping_semiprime_factors_using_dc1319_s24) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l25 trapping_semiprime_factors_using_dc1319_s24 trapping_semiprime_factors_using_dc1319_s25) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l26 trapping_semiprime_factors_using_dc1319_s25 trapping_semiprime_factors_using_dc1319_s26) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l27 trapping_semiprime_factors_using_dc1319_s26 trapping_semiprime_factors_using_dc1319_s27) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l28 trapping_semiprime_factors_using_dc1319_s27 trapping_semiprime_factors_using_dc1319_s28) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l29 trapping_semiprime_factors_using_dc1319_s28 trapping_semiprime_factors_using_dc1319_s29) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l30 trapping_semiprime_factors_using_dc1319_s29 trapping_semiprime_factors_using_dc1319_s30) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l31 trapping_semiprime_factors_using_dc1319_s30 trapping_semiprime_factors_using_dc1319_s31) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l32 trapping_semiprime_factors_using_dc1319_s31 trapping_semiprime_factors_using_dc1319_s32) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l33 trapping_semiprime_factors_using_dc1319_s32 trapping_semiprime_factors_using_dc1319_s33) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l34 trapping_semiprime_factors_using_dc1319_s33 trapping_semiprime_factors_using_dc1319_s34) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l35 trapping_semiprime_factors_using_dc1319_s34 trapping_semiprime_factors_using_dc1319_s35) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l36 trapping_semiprime_factors_using_dc1319_s35 trapping_semiprime_factors_using_dc1319_s36) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l37 trapping_semiprime_factors_using_dc1319_s36 trapping_semiprime_factors_using_dc1319_s37) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l38 trapping_semiprime_factors_using_dc1319_s37 trapping_semiprime_factors_using_dc1319_s38) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l39 trapping_semiprime_factors_using_dc1319_s38 trapping_semiprime_factors_using_dc1319_s39) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l40 trapping_semiprime_factors_using_dc1319_s39 trapping_semiprime_factors_using_dc1319_s40) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l41 trapping_semiprime_factors_using_dc1319_s40 trapping_semiprime_factors_using_dc1319_s41) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l42 trapping_semiprime_factors_using_dc1319_s41 trapping_semiprime_factors_using_dc1319_s42) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l43 trapping_semiprime_factors_using_dc1319_s42 trapping_semiprime_factors_using_dc1319_s43) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l44 trapping_semiprime_factors_using_dc1319_s43 trapping_semiprime_factors_using_dc1319_s44) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l45 trapping_semiprime_factors_using_dc1319_s44 trapping_semiprime_factors_using_dc1319_s45) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l46 trapping_semiprime_factors_using_dc1319_s45 trapping_semiprime_factors_using_dc1319_s46) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l47 trapping_semiprime_factors_using_dc1319_s46 trapping_semiprime_factors_using_dc1319_s47) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l48 trapping_semiprime_factors_using_dc1319_s47 trapping_semiprime_factors_using_dc1319_s48) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l49 trapping_semiprime_factors_using_dc1319_s48 trapping_semiprime_factors_using_dc1319_s49) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l50 trapping_semiprime_factors_using_dc1319_s49 trapping_semiprime_factors_using_dc1319_s50) (.arrow trapping_semiprime_factors_using_dc1319_l51 trapping_semiprime_factors_using_dc1319_s50 trapping_semiprime_factors_using_dc1319_s51)))))))))))))))))))))))))))))))))))))) (.seq (.arrow trapping_semiprime_factors_using_dc1319_l52 (tensorProduct trapping_semiprime_factors_using_dc1319_s14 trapping_semiprime_factors_using_dc1319_s51) trapping_semiprime_factors_using_dc1319_s52) (.arrow trapping_semiprime_factors_using_dc1319_l53 trapping_semiprime_factors_using_dc1319_s52 trapping_semiprime_factors_using_dc1319_s53))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def trapping_semiprime_factors_using_dc1319_true_arm : IGProtocol trapping_semiprime_factors_using_dc1319_initial trapping_semiprime_factors_using_dc1319_s53 :=
  (trapping_semiprime_factors_using_dc1319_protocol).restrictToEVALT

-- false arm
noncomputable def trapping_semiprime_factors_using_dc1319_false_arm : IGProtocol trapping_semiprime_factors_using_dc1319_initial trapping_semiprime_factors_using_dc1319_s53 :=
  (trapping_semiprime_factors_using_dc1319_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def trapping_semiprime_factors_using_dc1319_tier_ground : OuroboricityTier := TierFunctor.obj trapping_semiprime_factors_using_dc1319_initial
def trapping_semiprime_factors_using_dc1319_tier : OuroboricityTier := TierFunctor.obj trapping_semiprime_factors_using_dc1319_s53
#eval trapping_semiprime_factors_using_dc1319_tier_ground  -- tier of the ground (pre-transformation)
#eval trapping_semiprime_factors_using_dc1319_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem trapping_semiprime_factors_using_dc1319_frobenius :
    igFrobeniusAlg.mul trapping_semiprime_factors_using_dc1319_initial trapping_semiprime_factors_using_dc1319_initial = trapping_semiprime_factors_using_dc1319_initial :=
  igFrobAlg_self_fusion trapping_semiprime_factors_using_dc1319_initial

theorem trapping_semiprime_factors_using_dc1319_protocol_depth :
    trapping_semiprime_factors_using_dc1319_protocol.depth = 42 := by rfl

end Imscribing