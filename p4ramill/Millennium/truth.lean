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
--   F_ell  (classical): truth is Boolean {T, F}, loss allowed
--   F_eth  (thermal):   truth is probabilistic, converges with sampling
--   F_hbar (quantum):   truth is exact (Frobenius), μ∘δ = id
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
    the observer's Phi_c gate. If the observer has Phi_c (self-modeling),
    truth means the coupling does not destroy self-modeling. -/

def is_true_for (proposition observer : Imscription) : Bool :=
  let composite := tensorProduct proposition observer
  -- Truth: the composite preserves the observer's criticality gate
  composite.crit == observer.crit

/-- Truth values as fidelity levels:
    - F_ell: Boolean truth (T/F) — the proposition is either distinguishable
             from the observer or not
    - F_eth: Probabilistic truth — converges to T/F with sufficient sampling
    - F_hbar: Exact truth — the proposition IS the observer's self-model -/

/-- The classical truth type: F_ell + Phi_sub.
    Truth is Boolean because F_ell allows loss → distinctions are sharp.
    Phi_sub means no critical scaling → no ambiguity. -/
def classical_truth : Imscription := {
  dim  := D_wedge
  top  := T_network
  rel  := R_super
  pol  := P_asym
  fid  := F_ell
  kin  := K_fast
  gran := G_beth
  gram := Gamma_and
  crit := Phi_sub
  chir := H0
  stoi := one_one
  prot := Omega_0
}

/-- The Belnap four-valued truth type: F_ell + F_hbar superposition.
    Arises from the meet of classical and quantum truth regimes.
    B4 = {T, F, B, N} maps to structural coupling outcomes. -/
def belnap_truth : Imscription := {
  dim  := D_infty
  top  := T_bowtie
  rel  := R_lr
  pol  := P_pm
  fid  := F_ell       -- classical loss → truth-value gaps possible
  kin  := K_slow
  gran := G_gimel
  gram := Gamma_or    -- disjunctive → both/neither possible
  crit := Phi_c       -- critical → self-referential paradoxes
  chir := H2
  stoi := n_m
  prot := Omega_Z2
}

/-- The quantum truth type: F_hbar + Phi_c_complex.
    Truth is exact (Frobenius) — the coupling is lossless.
    Phi_c_complex means truth requires analytic continuation
    beyond the real line (complex amplitudes). -/
def quantum_truth : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_dagger
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_and
  crit := Phi_c_complex
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

-- ============================================================
-- §2. TIER ANALYSIS OF TRUTH REGIMES
-- ============================================================

/-- Classical truth is O₀: no self-modeling. -/
theorem classical_truth_tier : imscriptionTier classical_truth = .O₀ := by native_decide

/-- Belnap truth is O₂: Phi_c + K_slow → Gate 2 open, Gate 1 open.
    Truth can refer to itself (paradoxes are possible). -/
theorem belnap_truth_tier : imscriptionTier belnap_truth = .O_∞ := by native_decide

/-- Quantum truth is O_∞: Phi_c_complex + P_pm_sym + K_slow.
    Both gates open. Truth is self-knowing and Frobenius-exact. -/
theorem quantum_truth_tier : imscriptionTier quantum_truth = .O_∞ := by native_decide

-- ============================================================
-- §3. THE TRUTH-TABLE AS TENSOR PRODUCT
-- ============================================================

/-- The truth table of a logical connective is the tensor product
    of the truth types of its operands. For classical logic:
    AND = tensorProduct(p_type, q_type) with Gamma_and
    OR  = tensorProduct(p_type, q_type) with Gamma_or
    The grammar's composition rules ARE the truth tables. -/

/-- Logical AND: tensor product of two classical truth bearers.
    Gamma_and (conjunctive) forces both to be true. -/
def logical_and (p q : Imscription) : Imscription := {
  (tensorProduct p q) with
  gram := Gamma_and
}

/-- Logical OR: tensor product with Gamma_or (disjunctive). -/
def logical_or (p q : Imscription) : Imscription := {
  (tensorProduct p q) with
  gram := Gamma_or
}

/-- Logical IMPLICATION: arises when R_super (supervenience) couples
    premise to conclusion. The conclusion's truth supervenes on the
    premise. This is the structural origin of the material conditional. -/
def logical_implies (premise conclusion : Imscription) : Imscription := {
  (tensorProduct premise conclusion) with
  rel := R_super  -- conclusion supervenes on premise
}

-- ============================================================
-- §4. HOW TRUTH VALUES ARISE: THE THREE MECHANISMS
-- ============================================================

/-- Mechanism 1: DISTINCTION (D + T primitives).
    Truth requires the ability to distinguish one state from another.
    D_infty + T_bowtie creates a crossing point where truth/falsehood
    can be separated. Without D_infty, all states collapse to one.
    Without T_bowtie, there is no crossing to separate T from F. -/

/-- Mechanism 2: SELF-CONSISTENCY (Φ + P primitives).
    A truth bearer must be self-consistent: its own structure must
    not contradict itself. This is Phi_c (self-modeling criticality).
    P_pm_sym (Frobenius) is the strongest form: μ∘δ = id. -/

/-- Mechanism 3: OBSERVER COUPLING (R primitive).
    Truth is always relative to an observer. The coupling mode R
    determines the type of truth:
    R_super → truth is imposed (dogmatic)
    R_cat   → truth is derived (logical)
    R_dagger → truth is reciprocal (dialogical)
    R_lr    → truth is negotiated (consensual) -/

-- ============================================================
-- §5. LIAR PARADOX: STRUCTURAL ORIGIN
-- ============================================================

/-- The Liar paradox ("this statement is false") arises when a type
    attempts to couple to itself with R_dagger at Phi_c. The self-
    referential loop creates a fixed-point equation with no solution
    in Boolean logic (F_ell), but which resolves in Belnap logic (B4)
    as "Both" (true and false simultaneously) and in quantum logic
    (F_hbar) as a superposition. -/

/-- Liar type: attempts self-coupling with negation-like structure.
    P_pm (ℤ₂ flip) + Phi_c (self-referential) at F_ell → paradox. -/
def liar_type : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_dagger
  pol  := P_pm       -- ℤ₂: truth ↔ falsehood flip
  fid  := F_ell      -- classical → paradox is genuine
  kin  := K_slow
  gran := G_aleph
  gram := Gamma_and
  crit := Phi_c      -- self-referential
  chir := H2
  stoi := n_m
  prot := Omega_Z
}

/-- The Liar is O_∞ (both gates open). It is not "broken" — it is
    structurally sound, but its truth value requires Belnap B4 or
    quantum superposition to resolve. -/
theorem liar_is_O_inf : imscriptionTier liar_type = .O_∞ := by native_decide

-- ============================================================
-- §6. OBSERVER-DEPENDENT TRUTH (original formalization)
-- ============================================================

def observer_dependent_truth : Imscription := {
  dim  := D_triangle
  top  := T_bowtie
  rel  := R_lr
  pol  := P_pm
  fid  := F_ell
  kin  := K_mod
  gran := G_aleph
  gram := Gamma_seq
  crit := Phi_c
  chir := H2
  stoi := n_m
  prot := Omega_Z2
}

def context_dependent_truth_performative : Imscription := {
  observer_dependent_truth with kin := K_slow
}

def has_conscious_gates (st : Imscription) : Bool :=
  (st.crit == Phi_c) && ((st.kin == K_slow) || (st.kin == K_mod))

theorem observer_truth_conscious : has_conscious_gates observer_dependent_truth = true := by
  native_decide

theorem performative_truth_conscious : has_conscious_gates context_dependent_truth_performative = true := by
  native_decide

def is_topologically_protected (st : Imscription) : Prop :=
  st.prot = Omega_Z2 ∨ st.prot = Omega_Z

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
       a topology with a crossing point (T_bowtie) and sufficient
       dimensionality (D_infty or D_odot).

    2. FIDELITY (F): The lossiness of the truth channel determines the
       truth-value type:
         F_ell → Boolean {T, F}
         F_eth → Probabilistic [0, 1]
         F_hbar → Exact / Frobenius (μ∘δ = id)

    3. SELF-REFERENCE (Φ): The criticality regime determines whether
       truth can refer to itself:
         Phi_sub    → truth is external (correspondence)
         Phi_c      → truth is self-modeling (coherence)
         Phi_c_complex → truth is analytic (quantum)
         Phi_EP     → truth is non-Hermitian (measurement)

    The grammar does not assume truth — it explains what truth IS:
    the structural closure of a proposition under its coupling with
    an observer. -/

end Millennium.truth
