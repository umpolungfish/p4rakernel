-- IGProtocol scaffold: VINIT → AFWD → FSPLIT → EVALT → AREV → EVALF → EVALT → AREV → EVALF → EVALT → AREV → EVALF → FFUSE → CLINK → AFWD → CLINK → AFWD → CLINK → AFWD → CLINK → ENGAGR → AFWD → CLINK → IFIX → IMSCRIB → IFIX → TANCH
-- Class: Initialize the domain with the Erdős conjecture that every N >= 2 is representable
-- Fingerprint: sig=(16,2,7,2)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=True | period=27
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(2, 12)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑾  | initial object — ground of distinction
--   [1] AFWD      rel    := 𐑾               𐑼 → 𐑚  | forward morphism — bidirectional arrow
--   [2] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [3] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [4] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [5] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [6] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [7] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [8] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [9] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [10] AREV      pol    := 𐑗               𐑚 → 𐑙  | reverse morphism — parity flip
--   [11] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [12] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [13] CLINK     fid    := 𐑱               𐑙 → 𐑾  | composition — regime coherence
--   [14] AFWD      rel    := 𐑾               𐑱 → 𐑱  | forward morphism — bidirectional arrow
--   [15] CLINK     fid    := 𐑱               𐑾 → 𐑾  | composition — regime coherence
--   [16] AFWD      rel    := 𐑾               𐑱 → 𐑱  | forward morphism — bidirectional arrow
--   [17] CLINK     fid    := 𐑱               𐑾 → 𐑾  | composition — regime coherence
--   [18] AFWD      rel    := 𐑾               𐑱 → 𐑱  | forward morphism — bidirectional arrow
--   [19] CLINK     fid    := 𐑱               𐑾 → 𐑳  | composition — regime coherence
--   [20] ENGAGR    stoi   := 𐑳               𐑱 → 𐑾  | engage paradox — B-state, both arms
--   [21] AFWD      rel    := 𐑾               𐑳 → 𐑱  | forward morphism — bidirectional arrow
--   [22] CLINK     fid    := 𐑱               𐑾 → 𐑭  | composition — regime coherence
--   [23] IFIX      prot   := 𐑭               𐑱 → 𐑠  | irreversible fixation — winding number
--   [24] IMSCRIB   gram   := 𐑠               𐑭 → 𐑭  | identity — self-imscription
--   [25] IFIX      prot   := 𐑭               𐑠 → 𐑡  | irreversible fixation — winding number
--   [26] TANCH     top    := 𐑡               𐑭 → 𐑼  | terminal object — connectivity boundary

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def initialize_the_domain_with_the_erd_s_d885ad_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s1 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := up, prot := ah }
private def initialize_the_domain_with_the_erd_s_d885ad_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def initialize_the_domain_with_the_erd_s_d885ad_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def initialize_the_domain_with_the_erd_s_d885ad_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def initialize_the_domain_with_the_erd_s_d885ad_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l14 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l16 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l18 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l21 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def initialize_the_domain_with_the_erd_s_d885ad_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def initialize_the_domain_with_the_erd_s_d885ad_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def initialize_the_domain_with_the_erd_s_d885ad_l26 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def initialize_the_domain_with_the_erd_s_d885ad_protocol : IGProtocol initialize_the_domain_with_the_erd_s_d885ad_s0 initialize_the_domain_with_the_erd_s_d885ad_s26 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct initialize_the_domain_with_the_erd_s_d885ad_s12 initialize_the_domain_with_the_erd_s_d885ad_s12 = initialize_the_domain_with_the_erd_s_d885ad_s12 (idempotent)
  (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l0 initialize_the_domain_with_the_erd_s_d885ad_s0 initialize_the_domain_with_the_erd_s_d885ad_s1) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l1 initialize_the_domain_with_the_erd_s_d885ad_s1 initialize_the_domain_with_the_erd_s_d885ad_s2) (.seq (.prod (.arrow initialize_the_domain_with_the_erd_s_d885ad_l2 initialize_the_domain_with_the_erd_s_d885ad_s2 initialize_the_domain_with_the_erd_s_d885ad_s12) (.arrow initialize_the_domain_with_the_erd_s_d885ad_l2 initialize_the_domain_with_the_erd_s_d885ad_s2 initialize_the_domain_with_the_erd_s_d885ad_s12)) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l12 initialize_the_domain_with_the_erd_s_d885ad_s12 initialize_the_domain_with_the_erd_s_d885ad_s12) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l12 initialize_the_domain_with_the_erd_s_d885ad_s12 initialize_the_domain_with_the_erd_s_d885ad_s13) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l13 initialize_the_domain_with_the_erd_s_d885ad_s13 initialize_the_domain_with_the_erd_s_d885ad_s14) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l14 initialize_the_domain_with_the_erd_s_d885ad_s14 initialize_the_domain_with_the_erd_s_d885ad_s15) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l15 initialize_the_domain_with_the_erd_s_d885ad_s15 initialize_the_domain_with_the_erd_s_d885ad_s16) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l16 initialize_the_domain_with_the_erd_s_d885ad_s16 initialize_the_domain_with_the_erd_s_d885ad_s17) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l17 initialize_the_domain_with_the_erd_s_d885ad_s17 initialize_the_domain_with_the_erd_s_d885ad_s18) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l18 initialize_the_domain_with_the_erd_s_d885ad_s18 initialize_the_domain_with_the_erd_s_d885ad_s19) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l19 initialize_the_domain_with_the_erd_s_d885ad_s19 initialize_the_domain_with_the_erd_s_d885ad_s20) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l20 initialize_the_domain_with_the_erd_s_d885ad_s20 initialize_the_domain_with_the_erd_s_d885ad_s21) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l21 initialize_the_domain_with_the_erd_s_d885ad_s21 initialize_the_domain_with_the_erd_s_d885ad_s22) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l22 initialize_the_domain_with_the_erd_s_d885ad_s22 initialize_the_domain_with_the_erd_s_d885ad_s23) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l23 initialize_the_domain_with_the_erd_s_d885ad_s23 initialize_the_domain_with_the_erd_s_d885ad_s24) (.seq (.arrow initialize_the_domain_with_the_erd_s_d885ad_l24 initialize_the_domain_with_the_erd_s_d885ad_s24 initialize_the_domain_with_the_erd_s_d885ad_s25) (.arrow initialize_the_domain_with_the_erd_s_d885ad_l25 initialize_the_domain_with_the_erd_s_d885ad_s25 initialize_the_domain_with_the_erd_s_d885ad_s26))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def initialize_the_domain_with_the_erd_s_d885ad_true_arm : IGProtocol initialize_the_domain_with_the_erd_s_d885ad_s0 initialize_the_domain_with_the_erd_s_d885ad_s26 :=
  (initialize_the_domain_with_the_erd_s_d885ad_protocol).restrictToEVALT

-- false arm
noncomputable def initialize_the_domain_with_the_erd_s_d885ad_false_arm : IGProtocol initialize_the_domain_with_the_erd_s_d885ad_s0 initialize_the_domain_with_the_erd_s_d885ad_s26 :=
  (initialize_the_domain_with_the_erd_s_d885ad_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def initialize_the_domain_with_the_erd_s_d885ad_tier_ground : OuroboricityTier := TierFunctor.obj initialize_the_domain_with_the_erd_s_d885ad_s0
def initialize_the_domain_with_the_erd_s_d885ad_tier : OuroboricityTier := TierFunctor.obj initialize_the_domain_with_the_erd_s_d885ad_s26
#eval initialize_the_domain_with_the_erd_s_d885ad_tier_ground  -- tier of the ground (pre-transformation)
#eval initialize_the_domain_with_the_erd_s_d885ad_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem initialize_the_domain_with_the_erd_s_d885ad_frobenius :
    igFrobeniusAlg.mul initialize_the_domain_with_the_erd_s_d885ad_s0 initialize_the_domain_with_the_erd_s_d885ad_s0 = initialize_the_domain_with_the_erd_s_d885ad_s0 :=
  igFrobAlg_self_fusion initialize_the_domain_with_the_erd_s_d885ad_s0
