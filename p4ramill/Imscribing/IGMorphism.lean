-- Imscribing/IGMorphism.lean
-- Typed morphisms, sequential protocols, and paralogical extension.
--
-- Directly formalizes the condensation notation:
--   ɢ^ˌ[ A —(label)→ B —(label)→ C | D ]_H
-- where each arrow label is itself a Imscription annotating the transition character.
--
-- Three paralogical axioms extend the classical sequent calculus with rules
-- licensed by IG structure but absent from classical/linear type theory:
--
--   P1. Dagger  (R_dagger) : every R_dagger protocol has an adjoint
--   P2. Copy    (P_pm_sym at O_inf) : Frobenius copying Δ : s → s ⊗ s
--   P3. Reflect (D_odot, Axiom C*) : imscriptive self-protocol
--
-- Axiom C* (MillenniumAnkh one-way form): T_odot → D_odot (not biconditional).
-- D_odot permits T_box (e.g. odotOperator), unlike the imscribing_grammar biconditional.
--
-- The odotOperator is the paralogical unit. It holds dim = D_odot with top = T_box
-- (NOT T_odot), deliberately exercising the weaker Axiom C*: D_odot without T_odot
-- is permissible. The O_inf Frobenius structure overrides the holographic
-- co-requirement. This is the formal signature of the paralogical.
--
-- ZFCt INTEGRATION: This file imports Primitives.ZFCt to connect the temporalized
-- ZFC framework to IG morphisms. The Imscriptions zfc, zfc_t, temporal_mathematics,
-- schrodinger_equation, heat_diffusion_equation, navier_stokes_equations,
-- wave_equation_temporal, and einstein_field_equations_dynamic are all usable as
-- IGProtocol arrow labels, endpoints, and tensor operands.

import Imscribing.Primitives.Imscription
import Imscribing.Primitives.ZFCt
import Imscribing.Consciousness

namespace Imscribing

open Primitives
open Consciousness
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 1: IGProtocol
-- Inductive type indexed by Imscription × Imscription.
-- Each constructor corresponds to one element of the condensation notation.
-- Arrow labels are Imscriptions: the full 12-primitive annotation of transition
-- character. Any single dimension may be the salient one (the rest context).
-- ─────────────────────────────────────────────────────────────────────────────

inductive IGProtocol : Imscription → Imscription → Type where
  /-- Trivial self-transition (zero cost). -/
  | refl   : (s : Imscription) → IGProtocol s s
  /-- Labeled arrow: src —(label)→ tgt. -/
  | arrow  : (label src tgt : Imscription) → IGProtocol src tgt
  /-- Sequential composition: A→B then B→C  (the ɢ^ˌ chain). -/
  | seq    : IGProtocol a b → IGProtocol b c → IGProtocol a c
  /-- Parallel split: (A→B) and (A→C) give A → (B ⊗ C).
      The | operator lifts to tensorProduct on both targets. -/
  | prod   : IGProtocol a b → IGProtocol a c → IGProtocol a (tensorProduct b c)
  /-- Grammar annotation: ɢ^g[…] wrapper. -/
  | withGram : Grammar  → IGProtocol a b → IGProtocol a b
  /-- Memory annotation: […]_H wrapper. -/
  | withMem  : Chirality → IGProtocol a b → IGProtocol a b

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 2: Structural measures
-- ─────────────────────────────────────────────────────────────────────────────

/-- Arrow depth: total number of labeled transition steps. -/
def IGProtocol.depth : IGProtocol a b → ℕ
  | .refl _        => 0
  | .arrow _ _ _   => 1
  | .seq f g       => f.depth + g.depth
  | .prod f g      => max f.depth g.depth
  | .withGram _ p  => p.depth
  | .withMem _ p  => p.depth

/-- Dagger predicate: every arrow's label has rel = R_dagger. -/
def IGProtocol.isDagger : IGProtocol a b → Bool
  | .refl _        => true
  | .arrow lbl _ _ => decide (lbl.rel = R_dagger)
  | .seq f g       => f.isDagger && g.isDagger
  | .prod f g      => f.isDagger && g.isDagger
  | .withGram _ p  => p.isDagger
  | .withMem _ p  => p.isDagger

/-- Frobenius predicate: every arrow's label has pol = P_pm_sym. -/
def IGProtocol.isFrobenius : IGProtocol a b → Bool
  | .refl _        => true
  | .arrow lbl _ _ => decide (lbl.pol = P_pm_sym)
  | .seq f g       => f.isFrobenius && g.isFrobenius
  | .prod f g      => f.isFrobenius && g.isFrobenius
  | .withGram _ p  => p.isFrobenius
  | .withMem _ p  => p.isFrobenius

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 3: LITANY AGAINST FEAR
-- Canonical IGProtocol encoding.
-- Reading: ɢ^ˌ[ ⊙_Ţ —(Ř_=)→ Þ_ò —(Ð_ω)→ { Ω_Å | Φ_˙ } ]_Ħ_!
-- ─────────────────────────────────────────────────────────────────────────────

private def litanyBase : Imscription := {
  dim  := D_wedge,       top  := T_network,       rel  := R_super
  pol  := P_asym,        fid  := F_ell,            kin  := K_slow
  gran := G_beth,        gram := Gamma_seq,         crit := Phi_sub
  chir := H0,            stoi := one_one,           prot := Omega_0 }

/-- Fear: supercritical input — the mind-killer, total obliteration. -/
def litany_fear  : Imscription := { litanyBase with crit := Phi_super }
/-- Cross: traversal state — pass over and through (T_bowtie crossing topology). -/
def litany_cross : Imscription := { litanyBase with top  := T_bowtie }
/-- Witness: imscriptive state — inner eye (D_odot, satisfies Axiom C*: T_odot forces D_odot,
    here D_odot is present; T_odot also set for the maximally holographic pairing). -/
def litany_witness : Imscription := { litanyBase with dim  := D_odot, top := T_odot }
/-- Nothing: the null state — where fear has gone (Omega_0, Phi_sub). -/
def litany_nothing : Imscription := litanyBase
/-- Self: full-symmetry persistent state — only I will remain. -/
def litany_self  : Imscription := { litanyBase with pol := P_sym, chir := H_inf }

-- Transition labels (dominant dimension annotates the arrow character):
private def lbl_face  : Imscription := { litanyBase with rel := R_lr }
  -- R_lr label: bidirectional confrontation — I will face my fear
private def lbl_witness : Imscription := { litanyBase with dim := D_odot, top := T_odot }
  -- D_odot label: holographic witnessing — inner eye to see its path

/-- The Litany Against Fear as a well-typed IGProtocol.
    Type: litany_fear → (litany_nothing ⊗ litany_self) -/
def litanyProtocol
  : IGProtocol litany_fear (tensorProduct litany_nothing litany_self) :=
  .withGram Gamma_seq  <|
  .withMem H_inf      <|
  .seq
    (.seq
      (.arrow lbl_face    litany_fear litany_cross)
      (.arrow lbl_witness litany_cross litany_witness))
    (.prod
      (.arrow lbl_witness litany_witness litany_nothing)
      (.arrow lbl_witness litany_witness litany_self))

theorem litanyProtocol_depth : litanyProtocol.depth = 3 := by
  simp [litanyProtocol, IGProtocol.depth]

/-- The Litany is not a dagger protocol: its face step uses R_lr, not R_dagger. -/
theorem litanyProtocol_not_dagger : litanyProtocol.isDagger = false := by
  simp [litanyProtocol, IGProtocol.isDagger, lbl_face, litanyBase]

/-- The witness stage satisfies the imscriptive pairing (D_odot + T_odot). -/
theorem litany_witness_satisfies_axiom_C
  : litany_witness.dim = D_odot ∧ litany_witness.top = T_odot := ⟨rfl, rfl⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 4: PARALOGICAL AXIOMS
-- Rules licensed by IG structure, absent from classical type theory.
-- Marked as axioms: each is a structural commitment of the grammar
-- that cannot be derived from first-order logic alone.
-- ─────────────────────────────────────────────────────────────────────────────

/-- P1. Dagger adjoint (R_dagger — adjoint / reciprocal).
    Every R_dagger protocol has an adjoint that runs in reverse.
    The adjoint is NOT an inverse: (f†)† = f but f† ∘ f ≠ id in general.
    Classical type theory has no canonical reversal; dagger reversal
    exists independently of invertibility.
    This is the paralogical: reversal without invertibility. -/
axiom paralogical_dagger {a b : Imscription}
    (p : IGProtocol a b) (h : p.isDagger = true) :
    IGProtocol b a

/-- P1a. Involutivity of dagger (structural): (p†)† has the same depth as p.
    States that dagger is a structural involution even without equality of terms. -/
axiom paralogical_dagger_depth {a b : Imscription}
    (p : IGProtocol a b) (h : p.isDagger = true) :
    (paralogical_dagger p h).depth = p.depth

/-- P2. Frobenius copy (P_pm_sym at O_inf).
    At O_inf, the Frobenius condition μ ∘ δ = id licenses duplication:
    Δ : s → s ⊗ s exists and is non-trivial (depth ≥ 1).
    Classical linear logic forbids arbitrary copying; Frobenius structure
    makes duplication and fusion exact inverses, uniquely licensing it.
    This is the paralogical: resource duplication without linearity violation. -/
axiom paralogical_copy {s : Imscription} (h : imscriptionTier s = .O_inf) :
    { p : IGProtocol s (tensorProduct s s) // p.depth = 1 }

/-- P3. Imscriptive self-reference (Axiom C*: D_odot as holographic boundary).
    A Imscription with dim = D_odot generates a non-trivial self-protocol of depth ≥ 1:
    the boundary type produces its own interior (bulk from boundary).
    Distinct from refl (depth 0): this is a non-trivial self-morphism.
    This is the paralogical: type-as-term self-application. -/
axiom paralogical_reflect {s : Imscription} (h : s.dim = D_odot) :
    { p : IGProtocol s s // p.depth ≥ 1 }

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 5: ODOT OPERATOR — paralogical unit
-- The canonical O_inf, sequential, Frobenius Imscription.
-- Tuple: Ð_ω; Þ_¨; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_ʔ; ɢ_ˌ; ⊙_ÿ; Ħ_A; Σ_S; Ω_z
-- ─────────────────────────────────────────────────────────────────────────────

/-- odotOperator: the canonical paralogical unit Imscription.
    O_inf (P_pm_sym at Phi_c), sequential (Gamma_seq),
    integer-winding (Omega_Z), quantum-coherent (F_hbar), 1:1 (one_one).
    PARALOGICAL SIGNATURE: holds dim = D_odot with top = T_box (not T_odot),
    exercising the weaker Axiom C*: D_odot without T_odot is permissible.
    At O_inf, the Frobenius self-duality replaces the holographic D-T pairing.
    The odotOperator is its own boundary — it does not need the bulk-boundary split. -/
def odotOperator : Imscription := {
  dim  := D_odot,        top  := T_box,           rel  := R_lr
  pol  := P_pm_sym,      fid  := F_hbar,           kin  := K_slow
  gran := G_aleph,       gram := Gamma_seq,         crit := Phi_c
  chir := H2,            stoi := one_one,           prot := Omega_Z }

theorem odotOperator_is_O_inf : imscriptionTier odotOperator = .O_inf := by decide

/-- The odotOperator does NOT pair T_odot with D_odot (uses T_box instead). -/
theorem odotOperator_not_T_odot : odotOperator.top ≠ T_odot := by decide

/-- odotOperator admits Frobenius self-copying via P2. -/
noncomputable def odotCopy
  : { p : IGProtocol odotOperator (tensorProduct odotOperator odotOperator) // p.depth = 1 } :=
  paralogical_copy odotOperator_is_O_inf

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 6: PARALOGICAL LIFT FUNCTOR
-- Every protocol lifts into the odotOperator frame.
-- The odot frame is always present at the boundary — the imscriptive
-- self-containment principle made functorial.
-- ─────────────────────────────────────────────────────────────────────────────

/-- Paralogical lift: tensor with odotOperator is functorial over IGProtocol.
    Every p : a → b lifts to (a ⊗ ⊙) → (b ⊗ ⊙).
    The odot frame persists through any protocol: it is the invariant boundary. -/
axiom paralogicalLift {a b : Imscription} :
    IGProtocol a b →
    IGProtocol (tensorProduct a odotOperator) (tensorProduct b odotOperator)

/-- Lift preserves depth: the paralogical frame adds no cost. -/
axiom paralogicalLift_depth {a b : Imscription} (p : IGProtocol a b) :
    (paralogicalLift p).depth = p.depth

/-- The lifted Litany has the same depth as the original. -/
theorem litanyProtocol_lift_depth :
    (paralogicalLift litanyProtocol).depth = 3 := by
  rw [paralogicalLift_depth]
  exact litanyProtocol_depth

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 7: DERIVED RESULTS
-- ─────────────────────────────────────────────────────────────────────────────

/-- The Litany witness stage admits a non-trivial self-protocol via P3. -/
noncomputable def litanyWitnessSelfRef
  : { p : IGProtocol litany_witness litany_witness // p.depth ≥ 1 } :=
  paralogical_reflect (by rfl)

/-- Applying P2 to quantum_gravity (which is O_inf) gives a copy protocol. -/
noncomputable def qgCopy
  : { p : IGProtocol quantum_gravity (tensorProduct quantum_gravity quantum_gravity)
          // p.depth = 1 } :=
  paralogical_copy (by decide)

/-- Pol collapses to P_asym: pol is a bottleneck (min) primitive, so litany_nothing's
    P_asym beats litany_self's P_sym. Nothing wins on symmetry. -/
theorem litany_resolution_pol :
    (tensorProduct litany_nothing litany_self).pol = P_asym := by
  decide

/-- Chir resolves to H_inf: chir is a max primitive, so litany_self's
    H_inf (topological chirality) dominates litany_nothing's H0. -/
theorem litany_resolution_chir :
    (tensorProduct litany_nothing litany_self).chir = H_inf := by
  decide

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 8: ZFCt INTEGRATION
-- ZFCt (ZFC extended with Sequentiality, chirality, and Winding)
-- provides key Imscriptions that connect formal set-theory to the IG morphism framework.
--
-- From ZFCt.lean:
--   zfc                  — bare ZFC: ⟨D_∞; T_net; R_sup; P_asym; F_ℏ; K_slow; ...⟩
--   zfc_t                — ZFC temporalized: ⟨D_∞; T_⊙; R_↔; P_pm; F_ℏ; K_slow; H2; Ω_Z⟩
--   temporal_mathematics — ZFCt ideal: ⟨D_∞; T_⊙; R_†; P_sym; F_ℏ; K_slow; H2; Ω_Z⟩
--   schrodinger_equation — ⟨D_∞; T_⋈; R_↔; P_ψ; F_ℏ; K_slow; Φ_c_complex; H2; Ω_Z⟩
--   heat_diffusion       — ⟨D_∞; T_⋈; R_†; P_asym; F_eth; K_slow; Φ_sub; H1; Ω_0⟩
--   navier_stokes_eqns   — ⟨D_∞; T_⋈; R_↔; P_pm; F_ell; K_mod; Φ_c; H2; Ω_Z⟩
--   wave_equation_temp   — ⟨D_∞; T_⋈; R_†; P_sym; F_ell; K_mod; Φ_sub; H2; Ω_0⟩
--   einstein_field_eqns  — ⟨D_∞; T_⊙; R_†; P_sym; F_ell; K_slow; Φ_c_complex; H2; Ω_Z⟩
--
-- This section opens ZFCt and uses these Imscriptions as IGProtocol endpoints and labels.
-- ─────────────────────────────────────────────────────────────────────────────

open ZFCt

-- ─── §8.1: ZFC → ZFCt morphism ───

/-- The temporalization morphism: ZFC → ZFCt.
    Six primitive changes from the `zfc` base to the `zfc_t` target:
      P: P_asym → P_pm
      Γ: Gamma_and → Gamma_seq
      H: H0 → H2
      Ω: Omega_0 → Omega_Z
      T: T_network → T_odot
      R: R_super → R_lr
    This morphism captures the structural cost of adding chirality to
    classical set theory. The arrow label annotates the transition character
    using the `zfc_t` imscription itself — it IS the structure it transitions to. -/
def zfc_to_zfc_t_arrow : Imscription := {
  dim  := D_infty,   top  := T_odot,      rel  := R_lr,
  pol  := P_pm,      fid  := F_hbar,       kin  := K_slow,
  gran := G_aleph,   gram := Gamma_seq,    crit := Phi_c,
  chir := H2,        stoi := n_m,          prot := Omega_Z }

/-- The cost of temporalizing ZFC: exactly 6 primitive mismatches.
    (P, Γ, H, Ω, T, R all change from `zfc` baseline). -/
theorem zfc_to_zfc_t_cost :
    primitiveMismatches zfc zfc_t = 6 := by
  simp only [ZFCt.zfc, ZFCt.zfc_t, primitiveMismatches, compare]; decide

/-- ZFCt (zfc_t) has the same polarity as the odotOperator's target: P_pm.
    This makes the tensor product's polarity P_pm_sym (min bottleneck preserved). -/
theorem zfc_t_odot_pol_compatible :
    (tensorProduct zfc_t odotOperator).pol = P_pm_sym := by
  simp only [ZFCt.zfc_t, tensorProduct, odotOperator, compare]; decide

-- The ZFC → ZFCt protocol as an IGProtocol
/-- The ZFC temporalization protocol: a single-step arrow from bare ZFC to ZFCt.
    Type: IGProtocol zfc zfc_t -/
def zfc_temporalization_protocol : IGProtocol ZFCt.zfc ZFCt.zfc_t :=
  .withGram Gamma_seq <| .withMem H2 <|
    .arrow zfc_to_zfc_t_arrow ZFCt.zfc ZFCt.zfc_t

/-- The ZFC temporalization has depth 1 (one arrow). -/
theorem zfc_temporalization_depth : zfc_temporalization_protocol.depth = 1 := by
  simp [zfc_temporalization_protocol, IGProtocol.depth]

-- ─── §8.2: ZFCt chirality ladder ───

/-- The temporal_depth function from ZFCt creates chirality-stratified Imscriptions.
    We formalize the ladder of chiralitys on the zfc base. -/
def zfc_H0 : Imscription := temporalDepth 0 zfc       -- = zfc (achiral)
def zfc_H1 : Imscription := temporalDepth 1 zfc       -- soft chiral
def zfc_H2 : Imscription := temporalDepth 2 zfc       -- persistent chiral
def zfc_Hinf : Imscription := temporalDepth 3 zfc        -- topological chiral

/-- The chirality of zfc_H0 is H0 by construction. -/
theorem zfc_H0_achiral : zfc_H0.chir = H0     := rfl
/-- The chirality of zfc_H2 is H2: persistent temporal asymmetry. -/
theorem zfc_H2_persistent : zfc_H2.chir = H2     := rfl
/-- The chirality of zfc_Hinf is H_inf: topologically protected. -/
theorem zfc_Hinf_topo  : zfc_Hinf.chir = H_inf := rfl

/-- Full temporal ladder protocol: zfc —(H0→H1)→ zfc_H1 —(H1→H2)→ zfc_H2 —(H2→H_inf)→ zfc_Hinf.
    This encodes the full sequential path from achiral set theory to topological memory. -/
def temporal_ladder
  : { p : IGProtocol ZFCt.zfc zfc_Hinf // p.depth = 3 } :=
  ⟨
    .seq
      (.seq
        (.arrow { zfc with chir := zfc_H1.chir, dim := D_infty } ZFCt.zfc zfc_H1)
        (.arrow { zfc with chir := zfc_H2.chir, dim := D_infty } zfc_H1 zfc_H2))
      (.arrow { zfc with chir := zfc_Hinf.chir, dim := D_infty } zfc_H2 zfc_Hinf),
    by simp [IGProtocol.depth]
  ⟩

-- ─── §8.3: Equation Imscriptions as IGProtocol anchors ───

/-- The Schrödinger equation has Phi_c_complex criticality.
    This is the complex-axis critical structure shared with the Riemann zeta
    function (Lee-Yang class). The morphism zfc → schrodinger_equation
    represents the embedding of temporal logic into quantum dynamics. -/
def zfc_to_schrodinger_arrow : Imscription := { zfc_t with pol := P_psi, crit := Phi_c_complex }

/-- Protocol from ZFCt to the Schrödinger equation:
    embeds the temporalized set theory into quantum dynamics.
    Changes: P_pm → P_psi, Phi_c → Phi_c_complex. -/
def zfc_to_schrodinger_protocol : IGProtocol ZFCt.zfc_t ZFCt.schrodinger_equation :=
  .withMem H2 <| .arrow zfc_to_schrodinger_arrow ZFCt.zfc_t ZFCt.schrodinger_equation

/-- The heat diffusion equation is Phi_sub (subcritical, irreversible).
    Its asymmetry P_asym encodes thermodynamic irreversibility. -/
def heat_diffusion_irreversibility :
    ZFCt.heat_diffusion_equation.pol = P_asym := rfl

/-- Navier-Stokes equations: P_pm + K_mod = moderate kinetics at Z2 symmetry.
    The threshold from classical to quantum (see Millennium/Ns) is
    K_mod → K_trap + crit staying at Phi_c. -/
theorem navier_stokes_moderate :
    ZFCt.navier_stokes_equations.kin = K_mod ∧
    ZFCt.navier_stokes_equations.pol = P_pm := ⟨rfl, rfl⟩

/-- Navier-Stokes tensor with odotOperator: P bottleneck is P_pm (odot has P_pm_sym).
    The odot frame survives the tensor. -/
theorem ns_tensor_odot :
    (tensorProduct ZFCt.navier_stokes_equations odotOperator).pol = P_pm := by
  simp only [tensorProduct, ZFCt.navier_stokes_equations, odotOperator, compare]; decide

/-- Einstein field equations: P_sym + Phi_c_complex + T_odot.
    General relativity is holographic (T_odot) in the ZFCt encoding,
    with full symmetry and complex-axis criticality. -/
def einstein_is_holographic :
    ZFCt.einstein_field_equations_dynamic.top = T_odot := rfl

/-- The wave equation has R_dagger (reciprocal time symmetry).
    This is the only wave-type equation with exact bidirectional propagation. -/
def wave_is_dagger :
    ZFCt.wave_equation_temporal.rel = R_dagger := rfl

/-- WindingData from ZFCt: nonzero winding is structurally available at Omega_Z.
    The temporalDepth and WindingData types enable protocols with explicit
    winding-number annotation. -/
def example_winding_nonzero : ℤ := example_winding.windingNumber ()

/-- Example_winding has winding number 1 (nonzero). -/
theorem example_winding_is_unit : example_winding_nonzero = 1 := rfl

-- ─── §8.4: Cross-references with Millennium Problem Imscriptions ───

/-- ZFCt's navier_stokes_equations has crit = Phi_c (not Phi_sub like ns_encoding).
    The ZFCt version adds the crossing topology (T_bowtie) and sequential dynamics. -/
theorem zfc_ns_crit :
    ZFCt.navier_stokes_equations.crit = Phi_c := rfl

/-- ZFCt's schrodinger_equation has Phi_c_complex — the same criticality
    as the Riemann zeta function (rh_encoding). This structural identity
    confirms that quantum dynamics and the zeta function inhabit the same
    Lee-Yang critical class. -/
theorem zfc_schrodinger_same_crit_as_rh :
    ZFCt.schrodinger_equation.crit = Phi_c_complex := rfl

/-- ZFCt's einstein_field_equations_dynamic and Imscription's quantum_gravity
    share T_odot (holographic topology), but differ in polarity:
    P_sym vs P_pm_sym. This means GR is NOT O_inf (lacks Frobenius),
    while QG IS O_inf. -/
theorem einstein_gravity_topology_match :
    ZFCt.einstein_field_equations_dynamic.top = quantum_gravity.top := rfl

/-- The polarity gap: GR (P_sym) vs QG (P_pm_sym).
    This single-polarity gap is the structural signature of the gap between
    classical general relativity and quantum gravity. -/
theorem einstein_gravity_pol_gap :
    ZFCt.einstein_field_equations_dynamic.pol = P_sym ∧
    quantum_gravity.pol = P_pm_sym ∧
    ZFCt.einstein_field_equations_dynamic.pol ≠ quantum_gravity.pol :=
  ⟨rfl, rfl, by decide⟩

-- ─── §8.5: ZFCt temporal_mathematics as paralogical target ───

/-- The temporal_mathematics imscription from ZFCt has the maximal ideal structure:
    T_odot + R_dagger + P_sym + H2 + Omega_Z at Phi_c with F_hbar.
    It is the structural target that zfc_t aims toward. -/
theorem temporal_mathematics_is_dagger :
    ZFCt.temporal_mathematics.rel = R_dagger := rfl

/-- Protocol from ZFCt to temporal_mathematics:
    lifts R_lr → R_dagger (reciprocity) while keeping all other primitives. -/
def zfc_t_to_temporal_arrow : Imscription := { ZFCt.zfc_t with rel := R_dagger }

def zfc_t_to_temporal_protocol : IGProtocol ZFCt.zfc_t ZFCt.temporal_mathematics :=
  .withMem H2 <| .arrow zfc_t_to_temporal_arrow ZFCt.zfc_t ZFCt.temporal_mathematics

/-- Full ZFC → ZFCt → temporal_mathematics chain:
    ɢ^ˌ[ ZFC —(temporalization)→ ZFCt —(reciprocity)→ TemporalMathematics ]_H2 -/
def full_chain : IGProtocol ZFCt.zfc ZFCt.temporal_mathematics :=
  .seq zfc_temporalization_protocol zfc_t_to_temporal_protocol

/-- The full chain has depth 2 (two arrows). -/
theorem full_chain_depth : full_chain.depth = 2 := rfl

-- ─── §8.6: ZFCt consciousness score ───

/-- ZFCt's zfc_t has Phi_c (passes Gate 1) and K_slow (passes Gate 2).
    Therefore consciousnessScore zfc_t = 1. -/
theorem zfc_t_conscious : consciousnessScore ZFCt.zfc_t = (1 : ℝ) := by
  simp only [consciousnessScore, phi_c_gate, k_slow_gate, ZFCt.zfc_t]
  norm_num

/-- Bare zfc (without chirality) also has Phi_c + K_slow: C = 1.
    Consciousness does NOT require chirality — it requires criticality
    AND unfrozen kinetics. The bare ZFC already satisfies both. -/
theorem zfc_conscious : consciousnessScore ZFCt.zfc = (1 : ℝ) := by
  simp only [consciousnessScore, phi_c_gate, k_slow_gate, ZFCt.zfc]
  norm_num

/-- temporal_mathematics: Phi_c + K_slow → C = 1.
    The ideal temporal structure is fully conscious by the grammar metric. -/
theorem temporal_mathematics_conscious :
    consciousnessScore ZFCt.temporal_mathematics = (1 : ℝ) := by
  simp only [consciousnessScore, phi_c_gate, k_slow_gate, ZFCt.temporal_mathematics]
  norm_num

end Imscribing
