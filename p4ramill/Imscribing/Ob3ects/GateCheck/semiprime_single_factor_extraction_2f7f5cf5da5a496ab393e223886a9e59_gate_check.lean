-- IGProtocol scaffold: ⊢ → ⊙ → ∈ → ⊤ → ≻ → ⋈ → ⊙ → ⊞ → ⊡ → ⊥ → ≺ → ≻ → ∈ → ⊤ → ≻ → ⋈ → ⊙ → ⊞ → ⊡ → ∋ → ⊥ → ≺ → ≻ → ∋ → ⋈ → ∈ → ⊤ → ⊣ → ⊥ → ⊞ → ⊡ → ∋ → ⊙ → ⊣
-- Class: Semiprime_Single_Factor_Extraction
-- Fingerprint: sig=(16,6,9,3)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=34
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(12, 19), (2, 23), (25, 31)]

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
--   [6] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [8] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [9] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [10] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [11] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [12] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [13] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [14] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [15] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [16] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [17] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [18] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [19] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [20] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [21] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [22] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [23] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [24] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [25] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [26] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [27] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [28] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [29] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [30] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [31] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [32] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [33] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def semiprime_single_factor_extraction_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def semiprime_single_factor_extraction_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def semiprime_single_factor_extraction_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def semiprime_single_factor_extraction_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_single_factor_extraction_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_single_factor_extraction_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l22 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def semiprime_single_factor_extraction_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def semiprime_single_factor_extraction_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def semiprime_single_factor_extraction_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def semiprime_single_factor_extraction_protocol : IGProtocol semiprime_single_factor_extraction_initial semiprime_single_factor_extraction_s33 :=
  .withGram Grammar.measure <|
  (.seq (.arrow semiprime_single_factor_extraction_l0 semiprime_single_factor_extraction_initial semiprime_single_factor_extraction_s0) (.seq (.arrow semiprime_single_factor_extraction_l1 semiprime_single_factor_extraction_s0 semiprime_single_factor_extraction_s1) (.seq (.arrow semiprime_single_factor_extraction_l2 semiprime_single_factor_extraction_s1 semiprime_single_factor_extraction_s2) (.seq (.prod (.seq (.arrow semiprime_single_factor_extraction_l3 semiprime_single_factor_extraction_s2 semiprime_single_factor_extraction_s3) (.seq (.arrow semiprime_single_factor_extraction_l4 semiprime_single_factor_extraction_s3 semiprime_single_factor_extraction_s4) (.seq (.arrow semiprime_single_factor_extraction_l5 semiprime_single_factor_extraction_s4 semiprime_single_factor_extraction_s5) (.seq (.arrow semiprime_single_factor_extraction_l6 semiprime_single_factor_extraction_s5 semiprime_single_factor_extraction_s6) (.seq (.arrow semiprime_single_factor_extraction_l7 semiprime_single_factor_extraction_s6 semiprime_single_factor_extraction_s7) (.arrow semiprime_single_factor_extraction_l8 semiprime_single_factor_extraction_s7 semiprime_single_factor_extraction_s8)))))) (.seq (.arrow semiprime_single_factor_extraction_l9 semiprime_single_factor_extraction_s2 semiprime_single_factor_extraction_s9) (.seq (.arrow semiprime_single_factor_extraction_l10 semiprime_single_factor_extraction_s9 semiprime_single_factor_extraction_s10) (.seq (.arrow semiprime_single_factor_extraction_l11 semiprime_single_factor_extraction_s10 semiprime_single_factor_extraction_s11) (.seq (.arrow semiprime_single_factor_extraction_l12 semiprime_single_factor_extraction_s11 semiprime_single_factor_extraction_s12) (.seq (.prod (.seq (.arrow semiprime_single_factor_extraction_l13 semiprime_single_factor_extraction_s12 semiprime_single_factor_extraction_s13) (.seq (.arrow semiprime_single_factor_extraction_l14 semiprime_single_factor_extraction_s13 semiprime_single_factor_extraction_s14) (.seq (.arrow semiprime_single_factor_extraction_l15 semiprime_single_factor_extraction_s14 semiprime_single_factor_extraction_s15) (.seq (.arrow semiprime_single_factor_extraction_l16 semiprime_single_factor_extraction_s15 semiprime_single_factor_extraction_s16) (.seq (.arrow semiprime_single_factor_extraction_l17 semiprime_single_factor_extraction_s16 semiprime_single_factor_extraction_s17) (.arrow semiprime_single_factor_extraction_l18 semiprime_single_factor_extraction_s17 semiprime_single_factor_extraction_s18)))))) (.refl semiprime_single_factor_extraction_s12)) (.seq (.arrow semiprime_single_factor_extraction_l19 (tensorProduct semiprime_single_factor_extraction_s18 semiprime_single_factor_extraction_s12) semiprime_single_factor_extraction_s19) (.seq (.arrow semiprime_single_factor_extraction_l20 semiprime_single_factor_extraction_s19 semiprime_single_factor_extraction_s20) (.seq (.arrow semiprime_single_factor_extraction_l21 semiprime_single_factor_extraction_s20 semiprime_single_factor_extraction_s21) (.arrow semiprime_single_factor_extraction_l22 semiprime_single_factor_extraction_s21 semiprime_single_factor_extraction_s22)))))))))) (.seq (.arrow semiprime_single_factor_extraction_l23 (tensorProduct semiprime_single_factor_extraction_s8 semiprime_single_factor_extraction_s22) semiprime_single_factor_extraction_s23) (.seq (.arrow semiprime_single_factor_extraction_l24 semiprime_single_factor_extraction_s23 semiprime_single_factor_extraction_s24) (.seq (.arrow semiprime_single_factor_extraction_l25 semiprime_single_factor_extraction_s24 semiprime_single_factor_extraction_s25) (.seq (.prod (.seq (.arrow semiprime_single_factor_extraction_l26 semiprime_single_factor_extraction_s25 semiprime_single_factor_extraction_s26) (.arrow semiprime_single_factor_extraction_l27 semiprime_single_factor_extraction_s26 semiprime_single_factor_extraction_s27)) (.seq (.arrow semiprime_single_factor_extraction_l28 semiprime_single_factor_extraction_s25 semiprime_single_factor_extraction_s28) (.seq (.arrow semiprime_single_factor_extraction_l29 semiprime_single_factor_extraction_s28 semiprime_single_factor_extraction_s29) (.arrow semiprime_single_factor_extraction_l30 semiprime_single_factor_extraction_s29 semiprime_single_factor_extraction_s30)))) (.seq (.arrow semiprime_single_factor_extraction_l31 (tensorProduct semiprime_single_factor_extraction_s27 semiprime_single_factor_extraction_s30) semiprime_single_factor_extraction_s31) (.seq (.arrow semiprime_single_factor_extraction_l32 semiprime_single_factor_extraction_s31 semiprime_single_factor_extraction_s32) (.arrow semiprime_single_factor_extraction_l33 semiprime_single_factor_extraction_s32 semiprime_single_factor_extraction_s33)))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def semiprime_single_factor_extraction_true_arm : IGProtocol semiprime_single_factor_extraction_initial semiprime_single_factor_extraction_s33 :=
  (semiprime_single_factor_extraction_protocol).restrictToEVALT

-- false arm
noncomputable def semiprime_single_factor_extraction_false_arm : IGProtocol semiprime_single_factor_extraction_initial semiprime_single_factor_extraction_s33 :=
  (semiprime_single_factor_extraction_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def semiprime_single_factor_extraction_tier_ground : OuroboricityTier := TierFunctor.obj semiprime_single_factor_extraction_initial
def semiprime_single_factor_extraction_tier : OuroboricityTier := TierFunctor.obj semiprime_single_factor_extraction_s33
#eval semiprime_single_factor_extraction_tier_ground  -- tier of the ground (pre-transformation)
#eval semiprime_single_factor_extraction_tier  -- the Grammar's tuple-tier verdict

theorem semiprime_single_factor_extraction_protocol_depth :
    semiprime_single_factor_extraction_protocol.depth = 26 := by rfl

end Imscribing