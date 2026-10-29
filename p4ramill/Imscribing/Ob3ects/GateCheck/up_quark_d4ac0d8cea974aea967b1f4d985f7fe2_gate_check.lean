-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ≻ → ⋈ → ⊤ → ≺ → ⊞ → ⊥ → ∋ → ⊙ → ⊡ → ⊣ → ∈ → ≻ → ⋈ → ⊤ → ≺ → ⊞ → ⊥ → ∋ → ⊡ → ⊣ → ∈ → ≻ → ⋈ → ⊤ → ≺ → ⊞ → ⊥ → ∋ → ⊡ → ⊣ → ∈ → ≻ → ⋈ → ⊤ → ≺ → ⊞ → ⊥ → ∋ → ⊡ → ⊣ → ∈ → ≻ → ⋈ → ⊤ → ≺ → ⊞ → ⊥ → ∋ → ⊡ → ⊣ → ⊙ → ⊡
-- Class: up_quark
-- Fingerprint: sig=(24,10,15,6)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=55
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(2, 9), (13, 20), (23, 30), (33, 40), (43, 50)]

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
--   [3] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [4] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [5] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [6] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [7] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [8] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [9] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [13] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [14] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [15] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [16] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [17] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [18] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [19] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [20] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [21] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [22] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [23] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [24] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [25] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [26] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [27] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [28] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [29] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [30] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [31] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [32] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [33] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [34] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [35] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [36] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [37] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [38] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [39] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [40] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [41] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [42] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [43] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [44] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [45] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [46] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [47] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [48] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [49] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [50] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [51] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [52] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [53] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def up_quark_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def up_quark_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def up_quark_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def up_quark_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def up_quark_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def up_quark_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def up_quark_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def up_quark_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def up_quark_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def up_quark_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def up_quark_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def up_quark_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def up_quark_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def up_quark_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l24 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def up_quark_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def up_quark_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def up_quark_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l34 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def up_quark_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def up_quark_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def up_quark_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l44 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def up_quark_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l48 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def up_quark_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def up_quark_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def up_quark_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def up_quark_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def up_quark_protocol : IGProtocol up_quark_initial up_quark_s54 :=
  .withGram Grammar.measure <|
  (.seq (.arrow up_quark_l0 up_quark_initial up_quark_s0) (.seq (.arrow up_quark_l1 up_quark_s0 up_quark_s1) (.seq (.arrow up_quark_l2 up_quark_s1 up_quark_s2) (.seq (.prod (.seq (.arrow up_quark_l3 up_quark_s2 up_quark_s3) (.seq (.arrow up_quark_l4 up_quark_s3 up_quark_s4) (.seq (.arrow up_quark_l5 up_quark_s4 up_quark_s5) (.seq (.arrow up_quark_l6 up_quark_s5 up_quark_s6) (.arrow up_quark_l7 up_quark_s6 up_quark_s7))))) (.arrow up_quark_l8 up_quark_s2 up_quark_s8)) (.seq (.arrow up_quark_l9 (tensorProduct up_quark_s7 up_quark_s8) up_quark_s9) (.seq (.arrow up_quark_l10 up_quark_s9 up_quark_s10) (.seq (.arrow up_quark_l11 up_quark_s10 up_quark_s11) (.seq (.arrow up_quark_l12 up_quark_s11 up_quark_s12) (.seq (.arrow up_quark_l13 up_quark_s12 up_quark_s13) (.seq (.prod (.seq (.arrow up_quark_l14 up_quark_s13 up_quark_s14) (.seq (.arrow up_quark_l15 up_quark_s14 up_quark_s15) (.seq (.arrow up_quark_l16 up_quark_s15 up_quark_s16) (.seq (.arrow up_quark_l17 up_quark_s16 up_quark_s17) (.arrow up_quark_l18 up_quark_s17 up_quark_s18))))) (.arrow up_quark_l19 up_quark_s13 up_quark_s19)) (.seq (.arrow up_quark_l20 (tensorProduct up_quark_s18 up_quark_s19) up_quark_s20) (.seq (.arrow up_quark_l21 up_quark_s20 up_quark_s21) (.seq (.arrow up_quark_l22 up_quark_s21 up_quark_s22) (.seq (.arrow up_quark_l23 up_quark_s22 up_quark_s23) (.seq (.prod (.seq (.arrow up_quark_l24 up_quark_s23 up_quark_s24) (.seq (.arrow up_quark_l25 up_quark_s24 up_quark_s25) (.seq (.arrow up_quark_l26 up_quark_s25 up_quark_s26) (.seq (.arrow up_quark_l27 up_quark_s26 up_quark_s27) (.arrow up_quark_l28 up_quark_s27 up_quark_s28))))) (.arrow up_quark_l29 up_quark_s23 up_quark_s29)) (.seq (.arrow up_quark_l30 (tensorProduct up_quark_s28 up_quark_s29) up_quark_s30) (.seq (.arrow up_quark_l31 up_quark_s30 up_quark_s31) (.seq (.arrow up_quark_l32 up_quark_s31 up_quark_s32) (.seq (.arrow up_quark_l33 up_quark_s32 up_quark_s33) (.seq (.prod (.seq (.arrow up_quark_l34 up_quark_s33 up_quark_s34) (.seq (.arrow up_quark_l35 up_quark_s34 up_quark_s35) (.seq (.arrow up_quark_l36 up_quark_s35 up_quark_s36) (.seq (.arrow up_quark_l37 up_quark_s36 up_quark_s37) (.arrow up_quark_l38 up_quark_s37 up_quark_s38))))) (.arrow up_quark_l39 up_quark_s33 up_quark_s39)) (.seq (.arrow up_quark_l40 (tensorProduct up_quark_s38 up_quark_s39) up_quark_s40) (.seq (.arrow up_quark_l41 up_quark_s40 up_quark_s41) (.seq (.arrow up_quark_l42 up_quark_s41 up_quark_s42) (.seq (.arrow up_quark_l43 up_quark_s42 up_quark_s43) (.seq (.prod (.seq (.arrow up_quark_l44 up_quark_s43 up_quark_s44) (.seq (.arrow up_quark_l45 up_quark_s44 up_quark_s45) (.seq (.arrow up_quark_l46 up_quark_s45 up_quark_s46) (.seq (.arrow up_quark_l47 up_quark_s46 up_quark_s47) (.arrow up_quark_l48 up_quark_s47 up_quark_s48))))) (.arrow up_quark_l49 up_quark_s43 up_quark_s49)) (.seq (.arrow up_quark_l50 (tensorProduct up_quark_s48 up_quark_s49) up_quark_s50) (.seq (.arrow up_quark_l51 up_quark_s50 up_quark_s51) (.seq (.arrow up_quark_l52 up_quark_s51 up_quark_s52) (.seq (.arrow up_quark_l53 up_quark_s52 up_quark_s53) (.arrow up_quark_l54 up_quark_s53 up_quark_s54))))))))))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def up_quark_true_arm : IGProtocol up_quark_initial up_quark_s54 :=
  (up_quark_protocol).restrictToEVALT

-- false arm
noncomputable def up_quark_false_arm : IGProtocol up_quark_initial up_quark_s54 :=
  (up_quark_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def up_quark_tier_ground : OuroboricityTier := TierFunctor.obj up_quark_initial
def up_quark_tier : OuroboricityTier := TierFunctor.obj up_quark_s54
#eval up_quark_tier_ground  -- tier of the ground (pre-transformation)
#eval up_quark_tier  -- the Grammar's tuple-tier verdict

theorem up_quark_protocol_depth :
    up_quark_protocol.depth = 50 := by rfl

end Imscribing