-- IGProtocol scaffold: ⊢ → ⊙ → ⋈ → ∈ → ⊤ → ≻ → ⊞ → ⊥ → ≺ → ∋ → ⊙ → ⊡ → ⋈ → ∈ → ⊤ → ≻ → ⊞ → ⊥ → ≺ → ∋ → ⊙ → ⊡ → ⊡ → ⋈ → ∈ → ⊤ → ≻ → ⊞ → ⊥ → ≺ → ∋ → ⊙ → ⊡ → ⊡ → ⋈ → ∈ → ⊤ → ≻ → ⊞ → ⊥ → ≺ → ∋ → ⊙ → ⊡ → ⊡ → ⋈ → ∈ → ⊤ → ≻ → ⊞ → ⊥ → ≺ → ∋ → ⊙ → ⊡ → ⊡ → ⊣ → ⊙
-- Class: The_Prime_Number_Re_Entry_Whorl
-- Fingerprint: sig=(24,10,15,9)
--   self_ref=False | frobenius_order=3
--   dialetheia_complete=True | period=58
-- Expected tier: O₂dag
-- ∈/∋ pairs: [(3, 9), (13, 19), (24, 30), (35, 41), (46, 52)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] ⊢     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [3] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [5] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [6] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [7] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [8] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [9] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [10] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [12] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [13] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [14] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [15] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [16] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [17] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [18] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [19] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [20] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [21] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [22] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [23] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [24] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [25] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [26] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [27] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [28] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [29] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [30] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [31] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [32] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [33] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [34] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [35] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [36] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [37] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [38] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [39] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [40] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [41] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [42] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [43] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [44] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [45] ⋈     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [46] ∈    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [47] ⊤     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [48] ≻      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [49] ⊞    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [50] ⊥     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [51] ≺      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [52] ∋     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [53] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [54] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [55] ⊡      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [56] ⊣     top    := 𐑡               𐑡 → 𐑡  | terminal object — connectivity boundary
--   [57] ⊙   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def the_prime_number_re_entry_whorl_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s12 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s13 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s14 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s15 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s16 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s17 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s18 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s19 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s20 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s21 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s22 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s23 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s24 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s25 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s26 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s27 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s28 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s29 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s30 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s31 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s32 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s33 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s34 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s35 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s36 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s37 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s38 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s39 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s40 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s41 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s42 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s43 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s44 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s45 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s46 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s47 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s48 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s49 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s50 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s51 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def the_prime_number_re_entry_whorl_s52 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s53 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s54 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s55 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s56 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_s57 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def the_prime_number_re_entry_whorl_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l15 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l16 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_l17 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l18 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l19 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l20 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l21 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l22 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l23 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l24 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l25 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l26 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l27 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_l28 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l29 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l30 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l31 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l32 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l33 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l34 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l35 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l36 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l37 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l38 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_l39 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l40 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l41 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l42 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l43 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l44 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l45 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l46 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l47 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l48 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l49 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def the_prime_number_re_entry_whorl_l50 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l51 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l52 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l53 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l54 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l55 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def the_prime_number_re_entry_whorl_l56 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def the_prime_number_re_entry_whorl_l57 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def the_prime_number_re_entry_whorl_protocol : IGProtocol the_prime_number_re_entry_whorl_initial the_prime_number_re_entry_whorl_s57 :=
  .withGram Grammar.measure <|
  (.seq (.arrow the_prime_number_re_entry_whorl_l0 the_prime_number_re_entry_whorl_initial the_prime_number_re_entry_whorl_s0) (.seq (.arrow the_prime_number_re_entry_whorl_l1 the_prime_number_re_entry_whorl_s0 the_prime_number_re_entry_whorl_s1) (.seq (.arrow the_prime_number_re_entry_whorl_l2 the_prime_number_re_entry_whorl_s1 the_prime_number_re_entry_whorl_s2) (.seq (.arrow the_prime_number_re_entry_whorl_l3 the_prime_number_re_entry_whorl_s2 the_prime_number_re_entry_whorl_s3) (.seq (.prod (.seq (.arrow the_prime_number_re_entry_whorl_l4 the_prime_number_re_entry_whorl_s3 the_prime_number_re_entry_whorl_s4) (.seq (.arrow the_prime_number_re_entry_whorl_l5 the_prime_number_re_entry_whorl_s4 the_prime_number_re_entry_whorl_s5) (.arrow the_prime_number_re_entry_whorl_l6 the_prime_number_re_entry_whorl_s5 the_prime_number_re_entry_whorl_s6))) (.seq (.arrow the_prime_number_re_entry_whorl_l7 the_prime_number_re_entry_whorl_s3 the_prime_number_re_entry_whorl_s7) (.arrow the_prime_number_re_entry_whorl_l8 the_prime_number_re_entry_whorl_s7 the_prime_number_re_entry_whorl_s8))) (.seq (.arrow the_prime_number_re_entry_whorl_l9 (tensorProduct the_prime_number_re_entry_whorl_s6 the_prime_number_re_entry_whorl_s8) the_prime_number_re_entry_whorl_s9) (.seq (.arrow the_prime_number_re_entry_whorl_l10 the_prime_number_re_entry_whorl_s9 the_prime_number_re_entry_whorl_s10) (.seq (.arrow the_prime_number_re_entry_whorl_l11 the_prime_number_re_entry_whorl_s10 the_prime_number_re_entry_whorl_s11) (.seq (.arrow the_prime_number_re_entry_whorl_l12 the_prime_number_re_entry_whorl_s11 the_prime_number_re_entry_whorl_s12) (.seq (.arrow the_prime_number_re_entry_whorl_l13 the_prime_number_re_entry_whorl_s12 the_prime_number_re_entry_whorl_s13) (.seq (.prod (.seq (.arrow the_prime_number_re_entry_whorl_l14 the_prime_number_re_entry_whorl_s13 the_prime_number_re_entry_whorl_s14) (.seq (.arrow the_prime_number_re_entry_whorl_l15 the_prime_number_re_entry_whorl_s14 the_prime_number_re_entry_whorl_s15) (.arrow the_prime_number_re_entry_whorl_l16 the_prime_number_re_entry_whorl_s15 the_prime_number_re_entry_whorl_s16))) (.seq (.arrow the_prime_number_re_entry_whorl_l17 the_prime_number_re_entry_whorl_s13 the_prime_number_re_entry_whorl_s17) (.arrow the_prime_number_re_entry_whorl_l18 the_prime_number_re_entry_whorl_s17 the_prime_number_re_entry_whorl_s18))) (.seq (.arrow the_prime_number_re_entry_whorl_l19 (tensorProduct the_prime_number_re_entry_whorl_s16 the_prime_number_re_entry_whorl_s18) the_prime_number_re_entry_whorl_s19) (.seq (.arrow the_prime_number_re_entry_whorl_l20 the_prime_number_re_entry_whorl_s19 the_prime_number_re_entry_whorl_s20) (.seq (.arrow the_prime_number_re_entry_whorl_l21 the_prime_number_re_entry_whorl_s20 the_prime_number_re_entry_whorl_s21) (.seq (.arrow the_prime_number_re_entry_whorl_l22 the_prime_number_re_entry_whorl_s21 the_prime_number_re_entry_whorl_s22) (.seq (.arrow the_prime_number_re_entry_whorl_l23 the_prime_number_re_entry_whorl_s22 the_prime_number_re_entry_whorl_s23) (.seq (.arrow the_prime_number_re_entry_whorl_l24 the_prime_number_re_entry_whorl_s23 the_prime_number_re_entry_whorl_s24) (.seq (.prod (.seq (.arrow the_prime_number_re_entry_whorl_l25 the_prime_number_re_entry_whorl_s24 the_prime_number_re_entry_whorl_s25) (.seq (.arrow the_prime_number_re_entry_whorl_l26 the_prime_number_re_entry_whorl_s25 the_prime_number_re_entry_whorl_s26) (.arrow the_prime_number_re_entry_whorl_l27 the_prime_number_re_entry_whorl_s26 the_prime_number_re_entry_whorl_s27))) (.seq (.arrow the_prime_number_re_entry_whorl_l28 the_prime_number_re_entry_whorl_s24 the_prime_number_re_entry_whorl_s28) (.arrow the_prime_number_re_entry_whorl_l29 the_prime_number_re_entry_whorl_s28 the_prime_number_re_entry_whorl_s29))) (.seq (.arrow the_prime_number_re_entry_whorl_l30 (tensorProduct the_prime_number_re_entry_whorl_s27 the_prime_number_re_entry_whorl_s29) the_prime_number_re_entry_whorl_s30) (.seq (.arrow the_prime_number_re_entry_whorl_l31 the_prime_number_re_entry_whorl_s30 the_prime_number_re_entry_whorl_s31) (.seq (.arrow the_prime_number_re_entry_whorl_l32 the_prime_number_re_entry_whorl_s31 the_prime_number_re_entry_whorl_s32) (.seq (.arrow the_prime_number_re_entry_whorl_l33 the_prime_number_re_entry_whorl_s32 the_prime_number_re_entry_whorl_s33) (.seq (.arrow the_prime_number_re_entry_whorl_l34 the_prime_number_re_entry_whorl_s33 the_prime_number_re_entry_whorl_s34) (.seq (.arrow the_prime_number_re_entry_whorl_l35 the_prime_number_re_entry_whorl_s34 the_prime_number_re_entry_whorl_s35) (.seq (.prod (.seq (.arrow the_prime_number_re_entry_whorl_l36 the_prime_number_re_entry_whorl_s35 the_prime_number_re_entry_whorl_s36) (.seq (.arrow the_prime_number_re_entry_whorl_l37 the_prime_number_re_entry_whorl_s36 the_prime_number_re_entry_whorl_s37) (.arrow the_prime_number_re_entry_whorl_l38 the_prime_number_re_entry_whorl_s37 the_prime_number_re_entry_whorl_s38))) (.seq (.arrow the_prime_number_re_entry_whorl_l39 the_prime_number_re_entry_whorl_s35 the_prime_number_re_entry_whorl_s39) (.arrow the_prime_number_re_entry_whorl_l40 the_prime_number_re_entry_whorl_s39 the_prime_number_re_entry_whorl_s40))) (.seq (.arrow the_prime_number_re_entry_whorl_l41 (tensorProduct the_prime_number_re_entry_whorl_s38 the_prime_number_re_entry_whorl_s40) the_prime_number_re_entry_whorl_s41) (.seq (.arrow the_prime_number_re_entry_whorl_l42 the_prime_number_re_entry_whorl_s41 the_prime_number_re_entry_whorl_s42) (.seq (.arrow the_prime_number_re_entry_whorl_l43 the_prime_number_re_entry_whorl_s42 the_prime_number_re_entry_whorl_s43) (.seq (.arrow the_prime_number_re_entry_whorl_l44 the_prime_number_re_entry_whorl_s43 the_prime_number_re_entry_whorl_s44) (.seq (.arrow the_prime_number_re_entry_whorl_l45 the_prime_number_re_entry_whorl_s44 the_prime_number_re_entry_whorl_s45) (.seq (.arrow the_prime_number_re_entry_whorl_l46 the_prime_number_re_entry_whorl_s45 the_prime_number_re_entry_whorl_s46) (.seq (.prod (.seq (.arrow the_prime_number_re_entry_whorl_l47 the_prime_number_re_entry_whorl_s46 the_prime_number_re_entry_whorl_s47) (.seq (.arrow the_prime_number_re_entry_whorl_l48 the_prime_number_re_entry_whorl_s47 the_prime_number_re_entry_whorl_s48) (.arrow the_prime_number_re_entry_whorl_l49 the_prime_number_re_entry_whorl_s48 the_prime_number_re_entry_whorl_s49))) (.seq (.arrow the_prime_number_re_entry_whorl_l50 the_prime_number_re_entry_whorl_s46 the_prime_number_re_entry_whorl_s50) (.arrow the_prime_number_re_entry_whorl_l51 the_prime_number_re_entry_whorl_s50 the_prime_number_re_entry_whorl_s51))) (.seq (.arrow the_prime_number_re_entry_whorl_l52 (tensorProduct the_prime_number_re_entry_whorl_s49 the_prime_number_re_entry_whorl_s51) the_prime_number_re_entry_whorl_s52) (.seq (.arrow the_prime_number_re_entry_whorl_l53 the_prime_number_re_entry_whorl_s52 the_prime_number_re_entry_whorl_s53) (.seq (.arrow the_prime_number_re_entry_whorl_l54 the_prime_number_re_entry_whorl_s53 the_prime_number_re_entry_whorl_s54) (.seq (.arrow the_prime_number_re_entry_whorl_l55 the_prime_number_re_entry_whorl_s54 the_prime_number_re_entry_whorl_s55) (.seq (.arrow the_prime_number_re_entry_whorl_l56 the_prime_number_re_entry_whorl_s55 the_prime_number_re_entry_whorl_s56) (.arrow the_prime_number_re_entry_whorl_l57 the_prime_number_re_entry_whorl_s56 the_prime_number_re_entry_whorl_s57))))))))))))))))))))))))))))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def the_prime_number_re_entry_whorl_true_arm : IGProtocol the_prime_number_re_entry_whorl_initial the_prime_number_re_entry_whorl_s57 :=
  (the_prime_number_re_entry_whorl_protocol).restrictToEVALT

-- false arm
noncomputable def the_prime_number_re_entry_whorl_false_arm : IGProtocol the_prime_number_re_entry_whorl_initial the_prime_number_re_entry_whorl_s57 :=
  (the_prime_number_re_entry_whorl_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def the_prime_number_re_entry_whorl_tier_ground : OuroboricityTier := TierFunctor.obj the_prime_number_re_entry_whorl_initial
def the_prime_number_re_entry_whorl_tier : OuroboricityTier := TierFunctor.obj the_prime_number_re_entry_whorl_s57
#eval the_prime_number_re_entry_whorl_tier_ground  -- tier of the ground (pre-transformation)
#eval the_prime_number_re_entry_whorl_tier  -- the Grammar's tuple-tier verdict

theorem the_prime_number_re_entry_whorl_protocol_depth :
    the_prime_number_re_entry_whorl_protocol.depth = 48 := by rfl

end Imscribing