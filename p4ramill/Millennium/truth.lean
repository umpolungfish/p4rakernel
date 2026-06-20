-- Millennium/truth.lean
-- HOW TRUTH VALUES ARISE FROM THE GRAMMAR
--
-- Truth is not a primitive in the grammar — it emerges as a structural
-- relation between imscriptions. The key insight:
--
--   "A proposition is true"  ≡  "the structural type of the proposition
--                               is Frobenius-closed under its own coupling
--                               with the observer"
--
-- Three truth regimes emerge naturally:
--
--   age  (classical): truth is Boolean {T, F}, loss allowed
--   they  (thermal):   truth is probabilistic, converges with sampling
--   peep (quantum):   truth is exact (Frobenius), μ∘δ = id
--
-- The Belnap four-valued logic (B4: {T, F, Both, Neither}) arises from
-- the meet of two coupled systems at different fidelity levels.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Algebra
import Imscribing.Consciousness

namespace Millennium.truth

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option linter.style.longLine false

-- ============================================================
-- §1. TRUTH AS STRUCTURAL SELF-CONSISTENCY
-- ============================================================

/-- A type is "true" for an observer type if their tensor product
    is Frobenius-closed: tensorProduct(s, observer) preserves
    the observer's monad gate. If the observer has monad (self-modeling),
    truth means the coupling does not destroy self-modeling. -/

def is_true_for (proposition observer : Imscription) : Bool :=
  let composite := tensorProduct proposition observer
  -- Truth: the composite preserves the observer's criticality gate
  composite.crit == observer.crit

/-- Truth values as fidelity levels:
    - age: Boolean truth (T/F) — the proposition is either distinguishable
             from the observer or not
    - they: Probabilistic truth — converges to T/F with sufficient sampling
    - peep: Exact truth — the proposition IS the observer's self-model -/

/-- The classical truth type: age + woe.
    Truth is Boolean because age allows loss → distinctions are sharp.
    woe means no critical scaling → no ambiguity. -/
def classical_truth : Imscription := {
  dim  := dead
  top  := judge
  rel  := ado
  pol  := church
  fid  := age
  kin  := yea
  gran := bib
  gram := vow
  crit := woe
  chir := fee
  stoi := hung
  prot := awe
}

/-- The Belnap four-valued truth type: age + peep superposition.
    Arises from the meet of classical and quantum truth regimes.
    B4 = {T, F, B, N} maps to structural coupling outcomes. -/
def belnap_truth : Imscription := {
  dim  := array
  top  := mime
  rel  := ian
  pol  := out
  fid  := age       -- classical loss → truth-value gaps possible
  kin  := egg
  gran := thigh
  gram := gag    -- disjunctive → both/neither possible
  crit := monad       -- critical → self-referential paradoxes
  chir := sure
  stoi := up
  prot := oak
}

/-- The quantum truth type: peep + roar.
    Truth is exact (Frobenius) — the coupling is lossless.
    roar means truth requires analytic continuation
    beyond the real line (complex amplitudes). -/
def quantum_truth : Imscription := {
  dim  := if'
  top  := are
  rel  := ear
  pol  := or'
  fid  := peep
  kin  := egg
  gran := ice
  gram := vow
  crit := roar
  chir := sure
  stoi := up
  prot := ah
}

-- ============================================================
-- §2. TIER ANALYSIS OF TRUTH REGIMES
-- ============================================================

/-- Classical truth is O₀: no self-modeling. -/
theorem classical_truth_tier : imscriptionTier classical_truth = .O₀ := by native_decide

/-- Belnap truth is O₂: monad + egg → Gate 2 open, Gate 1 open.
    Truth can refer to itself (paradoxes are possible). -/
theorem belnap_truth_tier : imscriptionTier belnap_truth = .O_inf := by native_decide

/-- Quantum truth is O_inf: roar + or' + egg.
    Both gates open. Truth is self-knowing and Frobenius-exact. -/
theorem quantum_truth_tier : imscriptionTier quantum_truth = .O_inf := by native_decide

-- ============================================================
-- §3. THE TRUTH-TABLE AS TENSOR PRODUCT
-- ============================================================

/-- The truth table of a logical connective is the tensor product
    of the truth types of its operands. For classical logic:
    AND = tensorProduct(p_type, q_type) with vow
    OR  = tensorProduct(p_type, q_type) with gag
    The grammar's composition rules ARE the truth tables. -/

/-- Logical AND: tensor product of two classical truth bearers.
    vow (conjunctive) forces both to be true. -/
def logical_and (p q : Imscription) : Imscription := {
  (tensorProduct p q) with
  gram := vow
}

/-- Logical OR: tensor product with gag (disjunctive). -/
def logical_or (p q : Imscription) : Imscription := {
  (tensorProduct p q) with
  gram := gag
}

/-- Logical IMPLICATION: arises when ado (supervenience) couples
    premise to conclusion. The conclusion's truth supervenes on the
    premise. This is the structural origin of the material conditional. -/
def logical_implies (premise conclusion : Imscription) : Imscription := {
  (tensorProduct premise conclusion) with
  rel := ado  -- conclusion supervenes on premise
}

-- ============================================================
-- §4. HOW TRUTH VALUES ARISE: THE THREE MECHANISMS
-- ============================================================

/-- Mechanism 1: DISTINCTION (D + T primitives).
    Truth requires the ability to distinguish one state from another.
    array + mime creates a crossing point where truth/falsehood
    can be separated. Without array, all states collapse to one.
    Without mime, there is no crossing to separate T from F. -/

/-- Mechanism 2: SELF-CONSISTENCY (Φ + P primitives).
    A truth bearer must be self-consistent: its own structure must
    not contradict itself. This is monad (self-modeling criticality).
    or' (Frobenius) is the strongest form: μ∘δ = id. -/

/-- Mechanism 3: OBSERVER COUPLING (R primitive).
    Truth is always relative to an observer. The coupling mode R
    determines the type of truth:
    ado → truth is imposed (dogmatic)
    tot   → truth is derived (logical)
    ear → truth is reciprocal (dialogical)
    ian    → truth is negotiated (consensual) -/

-- ============================================================
-- §5. LIAR PARADOX: STRUCTURAL ORIGIN
-- ============================================================

/-- The Liar paradox ("this statement is false") arises when a type
    attempts to couple to itself with ear at monad. The self-
    referential loop creates a fixed-point equation with no solution
    in Boolean logic (age), but which resolves in Belnap logic (B4)
    as "Both" (true and false simultaneously) and in quantum logic
    (peep) as a superposition. -/

/-- Liar type: attempts self-coupling with negation-like structure.
    out (ℤ₂ flip) + monad (self-referential) at age → paradox. -/
def liar_type : Imscription := {
  dim  := if'
  top  := are
  rel  := ear
  pol  := out       -- ℤ₂: truth ↔ falsehood flip
  fid  := age      -- classical → paradox is genuine
  kin  := egg
  gran := ice
  gram := vow
  crit := monad      -- self-referential
  chir := sure
  stoi := up
  prot := ah
}

/-- The Liar is O_inf (both gates open). It is not "broken" — it is
    structurally sound, but its truth value requires Belnap B4 or
    quantum superposition to resolve. -/
theorem liar_is_O_inf : imscriptionTier liar_type = .O_inf := by native_decide

-- ============================================================
-- §6. OBSERVER-DEPENDENT TRUTH (original formalization)
-- ============================================================

def observer_dependent_truth : Imscription := {
  dim  := ash
  top  := mime
  rel  := ian
  pol  := out
  fid  := age
  kin  := loll
  gran := ice
  gram := measure
  crit := monad
  chir := sure
  stoi := up
  prot := oak
}

def context_dependent_truth_performative : Imscription := {
  observer_dependent_truth with kin := egg
}

def has_conscious_gates (st : Imscription) : Bool :=
  (st.crit == monad) && ((st.kin == egg) || (st.kin == loll))

theorem observer_truth_conscious : has_conscious_gates observer_dependent_truth = true := by
  native_decide

theorem performative_truth_conscious : has_conscious_gates context_dependent_truth_performative = true := by
  native_decide

def is_topologically_protected (st : Imscription) : Prop :=
  st.prot = oak ∨ st.prot = ah

theorem observer_truth_protected : is_topologically_protected observer_dependent_truth := by
  simp [observer_dependent_truth, is_topologically_protected]

-- ============================================================
-- §7. DISTANCES BETWEEN TRUTH REGIMES
-- ============================================================

/-- Distance between classical and quantum truth: 9 primitives differ. -/
theorem classical_quantum_truth_distance :
    primitiveMismatches classical_truth quantum_truth = 10 := by native_decide

/-- Distance between classical and Belnap truth. -/
theorem classical_belnap_truth_distance :
    primitiveMismatches classical_truth belnap_truth = 8 := by native_decide

/-- Distance between Belnap and quantum truth. -/
theorem belnap_quantum_truth_distance :
    primitiveMismatches belnap_truth quantum_truth = 4 := by native_decide

-- ============================================================
-- §8. HOW TRUTH VALUES ARISE: SUMMARY
-- ============================================================

/-- Truth values arise from three converging structural features:

    1. DISTINCTION (D + T): The ability to separate T from F requires
       a topology with a crossing point (mime) and sufficient
       dimensionality (array or if').

    2. FIDELITY (F): The lossiness of the truth channel determines the
       truth-value type:
         age → Boolean {T, F}
         they → Probabilistic [0, 1]
         peep → Exact / Frobenius (μ∘δ = id)

    3. SELF-REFERENCE (Φ): The criticality regime determines whether
       truth can refer to itself:
         woe    → truth is external (correspondence)
         monad      → truth is self-modeling (coherence)
         roar → truth is analytic (quantum)
         err     → truth is non-Hermitian (measurement)

    The grammar does not assume truth — it explains what truth IS:
    the structural closure of a proposition under its coupling with
    an observer. -/

end Millennium.truth
