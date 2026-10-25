-- IGProtocol scaffold: ⊢ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⋈ → ⊙ → ⊥ → ≺ → ⋈ → ⊞ → ∋ → ⊡ → ≻ → ∈ → ⊤ → ≻ → ⋈ → ⊥ → ≺ → ⋈ → ⊞ → ∋ → ⊡ → ⊙ → ≻ → ⋈ → ∈ → ⊤ → ≻ → ⋈ → ⊥ → ≺ → ⋈ → ⊞ → ∋ → ⊣ → ⊙ → ⊡
-- Class: elemental_germanium
-- Fingerprint: sig=(23,6,9,3)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=41
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(4, 13), (16, 24), (29, 37)]

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
--   [7] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [8] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [9] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [10] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [11] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [12] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [13] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [14] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [15] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [16] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [17] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [18] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [19] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [20] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [21] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [22] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [23] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [24] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [25] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [26] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [27] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [28] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [29] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [30] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [31] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [32] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [33] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [34] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [35] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [36] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [37] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [38] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [39] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [40] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number

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
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def elemental_germanium_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def elemental_germanium_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def elemental_germanium_s40 : Imscription :=
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
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l15 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def elemental_germanium_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l27 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l31 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def elemental_germanium_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def elemental_germanium_l37 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def elemental_germanium_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def elemental_germanium_protocol : IGProtocol elemental_germanium_initial elemental_germanium_s40 :=
  .withGram Grammar.measure <|
  (.seq (.arrow elemental_germanium_l0 elemental_germanium_initial elemental_germanium_s0) (.seq (.arrow elemental_germanium_l1 elemental_germanium_s0 elemental_germanium_s1) (.seq (.arrow elemental_germanium_l2 elemental_germanium_s1 elemental_germanium_s2) (.seq (.arrow elemental_germanium_l3 elemental_germanium_s2 elemental_germanium_s3) (.seq (.arrow elemental_germanium_l4 elemental_germanium_s3 elemental_germanium_s4) (.seq (.prod (.seq (.arrow elemental_germanium_l5 elemental_germanium_s4 elemental_germanium_s5) (.seq (.arrow elemental_germanium_l6 elemental_germanium_s5 elemental_germanium_s6) (.seq (.arrow elemental_germanium_l7 elemental_germanium_s6 elemental_germanium_s7) (.arrow elemental_germanium_l8 elemental_germanium_s7 elemental_germanium_s8)))) (.seq (.arrow elemental_germanium_l9 elemental_germanium_s4 elemental_germanium_s9) (.seq (.arrow elemental_germanium_l10 elemental_germanium_s9 elemental_germanium_s10) (.seq (.arrow elemental_germanium_l11 elemental_germanium_s10 elemental_germanium_s11) (.arrow elemental_germanium_l12 elemental_germanium_s11 elemental_germanium_s12))))) (.seq (.arrow elemental_germanium_l13 (tensorProduct elemental_germanium_s8 elemental_germanium_s12) elemental_germanium_s13) (.seq (.arrow elemental_germanium_l14 elemental_germanium_s13 elemental_germanium_s14) (.seq (.arrow elemental_germanium_l15 elemental_germanium_s14 elemental_germanium_s15) (.seq (.arrow elemental_germanium_l16 elemental_germanium_s15 elemental_germanium_s16) (.seq (.prod (.seq (.arrow elemental_germanium_l17 elemental_germanium_s16 elemental_germanium_s17) (.seq (.arrow elemental_germanium_l18 elemental_germanium_s17 elemental_germanium_s18) (.arrow elemental_germanium_l19 elemental_germanium_s18 elemental_germanium_s19))) (.seq (.arrow elemental_germanium_l20 elemental_germanium_s16 elemental_germanium_s20) (.seq (.arrow elemental_germanium_l21 elemental_germanium_s20 elemental_germanium_s21) (.seq (.arrow elemental_germanium_l22 elemental_germanium_s21 elemental_germanium_s22) (.arrow elemental_germanium_l23 elemental_germanium_s22 elemental_germanium_s23))))) (.seq (.arrow elemental_germanium_l24 (tensorProduct elemental_germanium_s19 elemental_germanium_s23) elemental_germanium_s24) (.seq (.arrow elemental_germanium_l25 elemental_germanium_s24 elemental_germanium_s25) (.seq (.arrow elemental_germanium_l26 elemental_germanium_s25 elemental_germanium_s26) (.seq (.arrow elemental_germanium_l27 elemental_germanium_s26 elemental_germanium_s27) (.seq (.arrow elemental_germanium_l28 elemental_germanium_s27 elemental_germanium_s28) (.seq (.arrow elemental_germanium_l29 elemental_germanium_s28 elemental_germanium_s29) (.seq (.prod (.seq (.arrow elemental_germanium_l30 elemental_germanium_s29 elemental_germanium_s30) (.seq (.arrow elemental_germanium_l31 elemental_germanium_s30 elemental_germanium_s31) (.arrow elemental_germanium_l32 elemental_germanium_s31 elemental_germanium_s32))) (.seq (.arrow elemental_germanium_l33 elemental_germanium_s29 elemental_germanium_s33) (.seq (.arrow elemental_germanium_l34 elemental_germanium_s33 elemental_germanium_s34) (.seq (.arrow elemental_germanium_l35 elemental_germanium_s34 elemental_germanium_s35) (.arrow elemental_germanium_l36 elemental_germanium_s35 elemental_germanium_s36))))) (.seq (.arrow elemental_germanium_l37 (tensorProduct elemental_germanium_s32 elemental_germanium_s36) elemental_germanium_s37) (.seq (.arrow elemental_germanium_l38 elemental_germanium_s37 elemental_germanium_s38) (.seq (.arrow elemental_germanium_l39 elemental_germanium_s38 elemental_germanium_s39) (.arrow elemental_germanium_l40 elemental_germanium_s39 elemental_germanium_s40))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def elemental_germanium_true_arm : IGProtocol elemental_germanium_initial elemental_germanium_s40 :=
  (elemental_germanium_protocol).restrictToEVALT

-- false arm
noncomputable def elemental_germanium_false_arm : IGProtocol elemental_germanium_initial elemental_germanium_s40 :=
  (elemental_germanium_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def elemental_germanium_tier_ground : OuroboricityTier := TierFunctor.obj elemental_germanium_initial
def elemental_germanium_tier : OuroboricityTier := TierFunctor.obj elemental_germanium_s40
#eval elemental_germanium_tier_ground  -- tier of the ground (pre-transformation)
#eval elemental_germanium_tier  -- the Grammar's tuple-tier verdict

theorem elemental_germanium_protocol_depth :
    elemental_germanium_protocol.depth = 31 := by rfl

end Imscribing