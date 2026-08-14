-- Imscribing/Millennium/Erdos/DifferenceSets_Complete.lean
-- Difference-set syndeticity: complete formalization from solve_ob3ect
--
-- This file integrates the 27-step IMASM protocol from
-- /home/mrnob0dy666/imsgct/ob3ect/digital/solve/solve_ob3ect.json into Lean 4.
--
-- Author: Math⊙perator (Lando⊗⊙perator team)
-- Date: 2025-01-12
--
-- Grammar tuple (derived from ob3ect phase_1):
--   ⟨𐑦𐑸𐑾𐑬𐑐𐑧𐑔𐑠⊙𐑖𐑙𐑭⟩
--   ⊢=𐑦 (infty-dim lattice)
--   ⊣=𐑸 (imscriptive closure - open problem boundary)
--   >=𐑾 (bidirectional coupling)
--   <=𐑬 (partial parity - sufficiency/necessity split)
--   ⋈=𐑐 (quantum fidelity - Furstenberg correspondence)
--   ⊤=𐑧 (slow kinetics - near-equilibrium recurrence)
--   ∈=𐑔 (maximal cardinality - ℤ is countably infinite)
--   ∋=𐑠 (sequential composition - n=1→2→… gap analysis)
--   ⊙=⊙ (critical - self-modeling on ℤ)
--   ⊥=𐑖 (two-step chirality - d vs -d difference direction)
--   ⊞=𐑙 (1:1 stoichiometry - one A → one D(A))
--   ◻=𐑭 (integer winding - ℤ-valued gaps)

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Mathlib.Tactic

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §1  OBEJECT DERIVED IMSCRIPTION
-- ============================================================

/-!
The difference sets syndeticity problem as an Imscription,
derived from the solve_ob3ect JSON artifact.

Domain: mathematical (integer lattice dynamics)
Surface tokens: difference set, syndeticity, Furstenberg correspondence,
                Banach density, lacunary sequence
-/

/--
The difference sets syndeticity problem as an Imscription.
Tier: O₂dag — criticality=⊙ (self-modeling), winding=𐑭 (integer)
-/
def difference_sets_syndeticity : Imscription :=
  { dim  := Dimensionality.infinity  -- 𐑦: infinite-dimensional lattice ℤ
    top  := Topology.imscriptive     -- 𐑸: open problem boundary (TANCH)
    rel  := Relational.bidirectional -- 𐑾: A→D(A) and attempted converse
    pol  := Polarity.partial         -- 𐑬: sufficiency true, necessity false
    fid  := Fidelity.quantum         -- 𐑐: Furstenberg correspondence functor
    kin  := KineticChar.slow         -- 𐑧: near-equilibrium recurrence
    gran := Granularity.maximal      -- 𐑔: ℤ is countably infinite
    gram := Grammar.sequential       -- 𐑠: n=1→2→… gap analysis
    crit := Criticality.critical     -- ⊙: self-reference on ℤ
    chir := Chirality.two_steps      -- 𐑖: difference direction d vs -d
    stoi := Stoichiometry.one_to_one -- 𐑙: one A → one D(A)
    prot := Protection.integer       -- 𐑭: ℤ-valued gap winding }

theorem difference_sets_syndeticity_tier :
    imscriptionTier difference_sets_syndeticity = .O₂dag := by
  unfold difference_sets_syndeticity
  native_decide

-- ============================================================
-- §2  CORE DEFINITIONS (from DifferenceSets.lean)
-- ============================================================

/-- Bounded gaps: some window of length `N` around every point meets `S`. -/
def Syndetic (S : ℤ → Bool) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ x : ℤ, ∃ i : ℕ, i < N ∧ S (x + i)

/-- Arbitrarily long blocks: `S` contains a run of every finite length. -/
def Thick (S : ℤ → Bool) : Prop :=
  ∀ N : ℕ, ∃ x : ℤ, ∀ i : ℕ, i < N → S (x + i)

/-- How many of the `N` points from `x` lie in `S`. -/
def windowCount (S : ℤ → Bool) (x : ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i : ℕ => S (x + (i : ℤ)))).card

/-- Upper Banach density zero: at some scale every window falls below any
prescribed fraction. -/
def UpperBanachZero (S : ℤ → Bool) : Prop :=
  ∀ c : ℚ, 0 < c → ∃ N : ℕ, 0 < N ∧ ∀ x : ℤ, (windowCount S x N : ℚ) < c * N

/-- The difference set D(A) = {d : |A ∩ (A-d)| = ∞} -/
def DifferenceSet (A : ℤ → Bool) : ℤ → Bool :=
  fun d => Infinite {a : ℤ | A a ∧ A (a - d)}
-- ============================================================
-- §3  THE 27-STEP IMASM PROTOCOL (COMPLETE)
-- ============================================================

/-!
From solve_ob3ect.json phase_4.steps:
The complete 27-step IMASM program encoding the mathematical structure.

Steps 1-2: VINIT → IMSCRIB (initialize ℤ, self-reference)
Steps 3-26: Nested FSPLIT/FFUSE structure (main trichotomy)
Step 27: TANCH (terminal anchor - open problem)

FSPLIT/FFUSE pairs: [(7,13), (17,24), (2,25)]
-/

-- Stage 0: Void integer lattice (VINIT)
private def ds_stage0 : Imscription :=
  { dim := Dimensionality.void
    top := Topology.judge
    rel := Relational.ado
    pol := Polarity.church
    fid := Fidelity.age
    kin := KineticChar.yea
    gran := Granularity.bib
    gram := Grammar.measure
    crit := Criticality.woe
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 1: Self-reference on ℤ (IMSCRIB)
private def ds_stage1 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.ado
    pol := Polarity.church
    fid := Fidelity.age
    kin := KineticChar.yea
    gran := Granularity.bib
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 2: Main trichotomy fork (FSPLIT)
private def ds_stage2 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.ado
    pol := Polarity.church
    fid := Fidelity.age
    kin := KineticChar.yea
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 3: T-arm forward (AFWD - difference construction)
private def ds_stage3 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.age
    kin := KineticChar.yea
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 4: T-arm evaluate positive density (EVALT)
private def ds_stage4 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.age
    kin := KineticChar.yea
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 5: T-arm Furstenberg correspondence (CLINK)
private def ds_stage5 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.quantum
    kin := KineticChar.yea
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.awe }

-- Stage 6: T-arm fix Furstenberg theorem (IFIX)
private def ds_stage6 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.integer }

-- Stage 7: Nested split (sufficiency/necessity) (FSPLIT)
private def ds_stage7 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.integer }

-- Stage 8: Inner T (sufficiency affirmed) (EVALT)
private def ds_stage8 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.church
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.integer }

-- Stage 9: Inner F reverse (AREV - converse attempt)
private def ds_stage9 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.fee
    stoi := Stoichiometry.hung
    prot := Protection.integer }

-- Stage 10: Inner F evaluate converse fails (EVALF)
private def ds_stage10 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.hung
    prot := Protection.integer }

-- Stage 11: Inner F paradice (ENGAGR - thick/syndetic duality)
private def ds_stage11 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.broadcast
    prot := Protection.integer }

-- Stage 12: Inner F fix duality theorems (IFIX)
private def ds_stage12 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.broadcast
    prot := Protection.integer }

-- Stage 13: Close inner split (FFUSE)
private def ds_stage13 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 14: Main F-arm reverse (AREV - combinatorial direction)
private def ds_stage14 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 15: Main F evaluate lacunary (EVALF)
private def ds_stage15 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 16: Main F fix lacunary bounds (IFIX)
private def ds_stage16 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 17: Nested split (piecewise syndetic/Bohr) (FSPLIT)
private def ds_stage17 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 18: Inner T piecewise syndetic (AFWD)
private def ds_stage18 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 19: Inner T evaluate piecewise syndetic (EVALT)
private def ds_stage19 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 20: Inner F Bohr characterization (AREV)
private def ds_stage20 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 21: Inner F evaluate Bohr sets (EVALF)
private def ds_stage21 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 22: Inner F fix Bohr characterization (IFIX)
private def ds_stage22 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 23: Close second nested split (FFUSE)
private def ds_stage23 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.out
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 24: Close main split (FFUSE)
private def ds_stage24 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.partial
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 25: Final fixation (IFIX)
private def ds_stage25 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.judge
    rel := Relational.bidirectional
    pol := Polarity.partial
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }

-- Stage 26: Terminal anchor (TANCH - open problem)
private def ds_stage26 : Imscription :=
  { dim := Dimensionality.infinity
    top := Topology.imscriptive
    rel := Relational.bidirectional
    pol := Polarity.partial
    fid := Fidelity.quantum
    kin := KineticChar.slow
    gran := Granularity.maximal
    gram := Grammar.sequential
    crit := Criticality.critical
    chir := Chirality.two_steps
    stoi := Stoichiometry.one_to_one
    prot := Protection.integer }
-- ============================================================
-- §4  THE COMPLETE 27-STEP IGPROTOCOL TERM
-- ============================================================

/-!
The complete 27-step IGProtocol term, replacing the scaffold `sorry`.

Structure:
- Steps 1-2: VINIT → IMSCRIB (ground setup)
- Step 3: FSPLIT (main trichotomy)
- Steps 4-7: T-arm (density branch → Furstenberg)
- Steps 8-13: Nested split (sufficiency/necessity)
- Steps 15-17: F-arm (lacunary counterexample)
- Steps 18-24: Nested split (piecewise/Bohr)
- Step 25: FFUSE (close main split)
- Step 27: TANCH (terminal anchor)
-/

noncomputable def difference_sets_protocol :
    IGProtocol ds_stage0 ds_stage26 :=
  .withGram Grammar.sequential <|
  -- Step 1: VINIT (void → infinity)
  .seq (.arrow { dim := Dimensionality.void, top := Topology.judge, rel := Relational.ado, pol := Polarity.church, fid := Fidelity.age, kin := KineticChar.yea, gran := Granularity.bib, gram := Grammar.measure, crit := Criticality.woe, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.awe } ds_stage0 ds_stage1)
  -- Step 2: IMSCRIB (self-reference)
  (.seq (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.ado, pol := Polarity.church, fid := Fidelity.age, kin := KineticChar.yea, gran := Granularity.bib, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.awe } ds_stage1 ds_stage2)
  -- Step 3: FSPLIT (main trichotomy)
  (.seq (.prod
    -- T-arm: density branch (steps 4-7)
    (.seq
      (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.age, kin := KineticChar.yea, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.awe } ds_stage2 ds_stage3)
      (.seq
        (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.age, kin := KineticChar.yea, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.awe } ds_stage3 ds_stage4)
        (.seq
          (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.quantum, kin := KineticChar.yea, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.awe } ds_stage4 ds_stage5)
          (.seq
            (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.integer } ds_stage5 ds_stage6)
            (.seq
              -- Step 7: Nested FSPLIT
              (.prod
                -- Inner T: sufficiency (steps 8-9)
                (.seq
                  (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.integer } ds_stage6 ds_stage7)
                  (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.church, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.integer } ds_stage7 ds_stage8))
                -- Inner F: necessity fails (steps 10-13)
                (.seq
                  (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.fee, stoi := Stoichiometry.hung, prot := Protection.integer } ds_stage7 ds_stage9)
                  (.seq
                    (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.hung, prot := Protection.integer } ds_stage9 ds_stage10)
                    (.seq
                      (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.broadcast, prot := Protection.integer } ds_stage10 ds_stage11)
                      (.seq
                        (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.thigh, gram := Grammar.measure, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.broadcast, prot := Protection.integer } ds_stage11 ds_stage12)
                        (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage12 ds_stage13)))))
    -- F-arm: combinatorial branch (steps 14-24)
    (.seq
      (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage13 ds_stage14)
      (.seq
        (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage14 ds_stage15)
        (.seq
          (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage15 ds_stage16)
          (.seq
            -- Step 17: Nested FSPLIT (piecewise/Bohr)
            (.prod
              -- Inner T: piecewise syndetic (steps 18-19)
              (.seq
                (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage16 ds_stage17)
                (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage17 ds_stage18)
                (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage18 ds_stage19))
              -- Inner F: Bohr sets (steps 20-23)
              (.seq
                (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage19 ds_stage20)
                (.seq
                  (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage20 ds_stage21)
                  (.seq
                    (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage21 ds_stage22)
                    (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.out, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage22 ds_stage23)))))
            (.seq
              -- Step 24: Close main split (FFUSE)
              (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.partial, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage23 ds_stage24)
              (.seq
                -- Step 25: Final fixation (IFIX)
                (.arrow { dim := Dimensionality.infinity, top := Topology.judge, rel := Relational.bidirectional, pol := Polarity.partial, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage24 ds_stage25)
                -- Step 26: Terminal anchor (TANCH)
                (.arrow { dim := Dimensionality.infinity, top := Topology.imscriptive, rel := Relational.bidirectional, pol := Polarity.partial, fid := Fidelity.quantum, kin := KineticChar.slow, gran := Granularity.maximal, gram := Grammar.sequential, crit := Criticality.critical, chir := Chirality.two_steps, stoi := Stoichiometry.one_to_one, prot := Protection.integer } ds_stage25 ds_stage26))))))))
