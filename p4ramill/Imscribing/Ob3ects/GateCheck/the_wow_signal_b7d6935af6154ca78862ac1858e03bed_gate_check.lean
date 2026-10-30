-- IGProtocol scaffold: ⊢ → ≻ → ⋈ → ⋈ → ⋈ → ⊙ → ⊤ → ∈ → ∈ → ≻ → ⊥ → ≻ → ⊥ → ≻ → ⊥ → ∋ → ≺ → ∈ → ≻ → ⊥ → ≻ → ⊥ → ≻ → ⊥ → ∋ → ≺ → ∈ → ≻ → ⊤ → ≻ → ⊥ → ≻ → ⊥ → ⊞ → ∋ → ∋ → ⊡ → ⋈ → ⋈ → ⋈ → ⋈ → ⋈ → ⊥ → ⊙ → ⊣ → ⊡
-- Class: the_WOW!_signal
-- Fingerprint: sig=(24,8,12,2)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=46
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(8, 15), (17, 24), (26, 34), (7, 35)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [2] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [3] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [6] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [7] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [8] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [9] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [10] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [11] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [12] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [13] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [14] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [15] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [16] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [17] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [18] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [19] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [20] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [21] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [24] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [25] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [26] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [27] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [28] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [29] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [30] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [33] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [34] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [35] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [36] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [37] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [38] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [39] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [40] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [41] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [42] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [43] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [44] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [45] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_wow_signal_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_wow_signal_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_wow_signal_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_wow_signal_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l9 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l13 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l20 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l27 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l29 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_wow_signal_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_wow_signal_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_wow_signal_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_wow_signal_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_wow_signal_protocol : IGProtocol the_wow_signal_initial the_wow_signal_s45 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_wow_signal_l0 the_wow_signal_initial the_wow_signal_s0) (.seq (.arrow the_wow_signal_l1 the_wow_signal_s0 the_wow_signal_s1) (.seq (.arrow the_wow_signal_l2 the_wow_signal_s1 the_wow_signal_s2) (.seq (.arrow the_wow_signal_l3 the_wow_signal_s2 the_wow_signal_s3) (.seq (.arrow the_wow_signal_l4 the_wow_signal_s3 the_wow_signal_s4) (.seq (.arrow the_wow_signal_l5 the_wow_signal_s4 the_wow_signal_s5) (.seq (.arrow the_wow_signal_l6 the_wow_signal_s5 the_wow_signal_s6) (.seq (.arrow the_wow_signal_l7 the_wow_signal_s6 the_wow_signal_s7) (.seq (.prod (.refl the_wow_signal_s7) (.seq (.arrow the_wow_signal_l8 the_wow_signal_s7 the_wow_signal_s8) (.seq (.prod (.arrow the_wow_signal_l9 the_wow_signal_s8 the_wow_signal_s9) (.seq (.arrow the_wow_signal_l10 the_wow_signal_s8 the_wow_signal_s10) (.seq (.arrow the_wow_signal_l11 the_wow_signal_s10 the_wow_signal_s11) (.seq (.arrow the_wow_signal_l12 the_wow_signal_s11 the_wow_signal_s12) (.seq (.arrow the_wow_signal_l13 the_wow_signal_s12 the_wow_signal_s13) (.arrow the_wow_signal_l14 the_wow_signal_s13 the_wow_signal_s14)))))) (.seq (.arrow the_wow_signal_l15 (tensorProduct the_wow_signal_s9 the_wow_signal_s14) the_wow_signal_s15) (.seq (.arrow the_wow_signal_l16 the_wow_signal_s15 the_wow_signal_s16) (.seq (.arrow the_wow_signal_l17 the_wow_signal_s16 the_wow_signal_s17) (.seq (.prod (.arrow the_wow_signal_l18 the_wow_signal_s17 the_wow_signal_s18) (.seq (.arrow the_wow_signal_l19 the_wow_signal_s17 the_wow_signal_s19) (.seq (.arrow the_wow_signal_l20 the_wow_signal_s19 the_wow_signal_s20) (.seq (.arrow the_wow_signal_l21 the_wow_signal_s20 the_wow_signal_s21) (.seq (.arrow the_wow_signal_l22 the_wow_signal_s21 the_wow_signal_s22) (.arrow the_wow_signal_l23 the_wow_signal_s22 the_wow_signal_s23)))))) (.seq (.arrow the_wow_signal_l24 (tensorProduct the_wow_signal_s18 the_wow_signal_s23) the_wow_signal_s24) (.seq (.arrow the_wow_signal_l25 the_wow_signal_s24 the_wow_signal_s25) (.seq (.arrow the_wow_signal_l26 the_wow_signal_s25 the_wow_signal_s26) (.seq (.prod (.seq (.arrow the_wow_signal_l27 the_wow_signal_s26 the_wow_signal_s27) (.seq (.arrow the_wow_signal_l28 the_wow_signal_s27 the_wow_signal_s28) (.arrow the_wow_signal_l29 the_wow_signal_s28 the_wow_signal_s29))) (.seq (.arrow the_wow_signal_l30 the_wow_signal_s26 the_wow_signal_s30) (.seq (.arrow the_wow_signal_l31 the_wow_signal_s30 the_wow_signal_s31) (.seq (.arrow the_wow_signal_l32 the_wow_signal_s31 the_wow_signal_s32) (.arrow the_wow_signal_l33 the_wow_signal_s32 the_wow_signal_s33))))) (.arrow the_wow_signal_l34 (tensorProduct the_wow_signal_s29 the_wow_signal_s33) the_wow_signal_s34)))))))))))) (.seq (.arrow the_wow_signal_l35 (tensorProduct the_wow_signal_s7 the_wow_signal_s34) the_wow_signal_s35) (.seq (.arrow the_wow_signal_l36 the_wow_signal_s35 the_wow_signal_s36) (.seq (.arrow the_wow_signal_l37 the_wow_signal_s36 the_wow_signal_s37) (.seq (.arrow the_wow_signal_l38 the_wow_signal_s37 the_wow_signal_s38) (.seq (.arrow the_wow_signal_l39 the_wow_signal_s38 the_wow_signal_s39) (.seq (.arrow the_wow_signal_l40 the_wow_signal_s39 the_wow_signal_s40) (.seq (.arrow the_wow_signal_l41 the_wow_signal_s40 the_wow_signal_s41) (.seq (.arrow the_wow_signal_l42 the_wow_signal_s41 the_wow_signal_s42) (.seq (.arrow the_wow_signal_l43 the_wow_signal_s42 the_wow_signal_s43) (.seq (.arrow the_wow_signal_l44 the_wow_signal_s43 the_wow_signal_s44) (.arrow the_wow_signal_l45 the_wow_signal_s44 the_wow_signal_s45))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_wow_signal_true_arm : IGProtocol the_wow_signal_initial the_wow_signal_s45 :=
  (the_wow_signal_protocol).restrictToEVALT

-- false arm
noncomputable def the_wow_signal_false_arm : IGProtocol the_wow_signal_initial the_wow_signal_s45 :=
  (the_wow_signal_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_wow_signal_tier_ground : OuroboricityTier := TierFunctor.obj the_wow_signal_initial
def the_wow_signal_tier : OuroboricityTier := TierFunctor.obj the_wow_signal_s45
#eval the_wow_signal_tier_ground  -- tier of the ground (pre-transformation)
#eval the_wow_signal_tier  -- the Grammar's tuple-tier verdict

theorem the_wow_signal_protocol_depth :
    the_wow_signal_protocol.depth = 41 := by rfl

end Imscribing