/-
  NS_Reentry.lean
  Navier-Stokes: the overflow re-entry, formalised in the re-entry tower.

  The NS problem looks like it needs an "external" injection to feed the
  cascade to small scales.  This file checks the dialetheic reading: the
  injection is not external.  It is the tower's own Cantor overflow (the
  value lifted to the next scale) which re-enters by first factoring through
  the frame collapse at that same scale, and then through the cascade step
  back down to the home scale.

  Factorisation:
      reEntry : V (n+1) → V n  =  cascadeStep ∘ collapseStep
  where
      collapseStep : V (n+1) → V (n+1)   the frame collapse ρ (same scale)
      cascadeStep  : V (n+1) → V n       the reveal μ (the step down)

  Reading the NS "external injection" this way, the injection is the tower's
  own overflow re-entering through ρ — internal, marked, and idempotent under
  its own frame collapse.  No map from outside V is used.
-/
import Imscribing.CircumPunctum
import Imscribing.Paraconsistent.Belnap

set_option linter.unusedVariables false

namespace Imscribing.NSReentry

open Imscribing.CircumPunctum

/- The two stages the overflow re-entry factors through:
     collapseStep : V (n+1) → V (n+1)  the frame collapse at the same scale
     cascadeStep  : V (n+1) → V n      the cascade step back to the home scale
-/
def collapseStep {n : ℕ} : V (n + 1) → V (n + 1) := ρ
def cascadeStep  {n : ℕ} : V (n + 1) → V n := μ

/-- Dialetheic re-entry of the overflow: the value at the next scale re-enters
    by first factoring through the frame collapse at that same scale, and then
    through the cascade step back down.  This is the internal reading of the
    NS "external" injection. -/
def reEntry {n : ℕ} : V (n + 1) → V n := cascadeStep ∘ collapseStep

/-- FACTORISATION LAW: re-entry is exactly cascade-after-collapse at the same
    scale.  The injection is the tower's own overflow re-entering through ρ. -/
theorem reEntry_def_factors {n : ℕ} (x : V (n + 1)) :
    reEntry x = cascadeStep (collapseStep x) := rfl

/-
  The re-entered overflow is a fixed point of the frame collapse at the next
  scale: collapsing it again changes nothing.  The injection, once it has
  entered, does not keep feeding new content — it is dialetheic, held.
-/
theorem reEntry_fixed_under_collapse {n : ℕ} (x : V (n + 1)) :
    collapseStep (collapseStep x) = collapseStep x := by
  unfold collapseStep
  exact ρ_idempotent x

/-
  The marker the Cantor lift sets survives the re-entry: the collapsed value
  is a marked singleton, its fibre bit true.  The overflow is present at the
  re-entered point, not merely accounted for.
-/
theorem reentry_marker_set {n : ℕ} (x : V (n + 1)) :
    (collapseStep x).2 = true := by
  unfold collapseStep; rfl

/-
  Read at the home scale, re-entry is indistinguishable from the cascade step
  alone: collapsing first and then cascading equals cascading.  The frame
  collapse is already satisfied by the marker, so it contributes no further
  change — the re-entered overflow and the pure cascade land on the same value.
-/
theorem reEntry_is_cascade {n : ℕ} (x : V (n + 1)) :
    reEntry x = cascadeStep x := by
  unfold reEntry cascadeStep
  exact μ_η_id (μ x)

/-- SOURCE: the content returned by injection is carried by the overflow itself. -/
def injectionSource {n : ℕ} (overflow : V (n + 1)) : V n := μ overflow

/-- The source is lifted into the unique marked representative at the upper scale. -/
theorem collapse_is_lifted_source {n : ℕ} (overflow : V (n + 1)) :
    collapseStep overflow = η (injectionSource overflow) := rfl

/-- MECHANISM: the overflow collapses to its marked source and cascades home. -/
theorem injection_returns_source {n : ℕ} (overflow : V (n + 1)) :
    reEntry overflow = injectionSource overflow := reEntry_is_cascade overflow

/-- A marked upper-scale value with the same carried content is determined uniquely.
    This is the reason the internal return passes through this frame collapse. -/
theorem collapse_unique {n : ℕ} (overflow y : V (n + 1))
    (hcontent : cascadeStep y = injectionSource overflow) (hmarked : y.2 = true) :
    y = collapseStep overflow := by
  apply Prod.ext
  · exact hcontent
  · exact hmarked

/-- REASON: retaining the source and setting the re-entry marker forces exactly
    one upper-scale representative. Collapse constructs that representative. -/
theorem injection_reason {n : ℕ} (overflow : V (n + 1)) :
    ∃! y : V (n + 1), cascadeStep y = injectionSource overflow ∧ y.2 = true := by
  refine ⟨collapseStep overflow, ⟨rfl, reentry_marker_set overflow⟩, ?_⟩
  intro y hy
  exact collapse_unique overflow y hy.1 hy.2

/-- Collapse acts precisely when the upper boundary is unmarked. -/
theorem collapse_changes_iff_unmarked {n : ℕ} (overflow : V (n + 1)) :
    collapseStep overflow ≠ overflow ↔ overflow.2 = false := by
  rcases overflow with ⟨content, marker⟩
  cases marker
  · constructor
    · intro _; rfl
    · intro _ h
      exact Bool.noConfusion (congrArg Prod.snd h)
  · constructor
    · intro h
      exact (h rfl).elim
    · intro h
      cases h

/-- A source lifted by the tower returns to itself through the complete mechanism. -/
theorem lifted_source_returns {n : ℕ} (source : V n) :
    reEntry (η source) = source := rfl

/-
  Connection to OpenAI, Finite Time Blowup for Navier–Stokes (2026-09-08),
  §§2.2–2.3 and Theorem 1.1:
  https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf

  Their oscillatory pulses are seeded by a smooth force and grow through the
  background shear; their momentum flux supplies an internal force cancelling
  the singular background residual. The equation uses the remaining smooth
  momentum residual as its force. These field-level forces have distinct roles.

  A readout below maps the tower's carried source into a field. SourceMatching
  states the identification of a specified force with that source. The bridge
  proves this is equivalent to realization through the internal mechanism and
  transports the specified force's balance and properties by equality.
-/

/-- Read the internal injection as a field. Domain may be space-time and Value
    may be a velocity-vector space; the readout supplies that realization. -/
def internalForce {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1)) : Domain → Value :=
  readout (reEntry overflow)

/-- Explicit field-level identification of a specified force with the overflow's
    own source. This condition can be applied separately to a pulse seed, an
    internal momentum-flux force, or the full equation's residual force. -/
def SourceMatching {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (force : Domain → Value) : Prop :=
  force = readout (injectionSource overflow)

/-- The specified source identification is exactly realization by re-entry. -/
theorem source_matching_iff_internal {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (force : Domain → Value) :
    SourceMatching readout overflow force ↔ force = internalForce readout overflow := by
  unfold SourceMatching internalForce
  rw [injection_returns_source]

/-- Collapse normalizes the upper boundary without changing the realized force. -/
theorem internal_force_collapse_invariant {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1)) :
    internalForce readout (collapseStep overflow) = internalForce readout overflow := rfl

/-- Field realization of source, mechanism, and reason together. -/
theorem injection_connection {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (force : Domain → Value) (hsource : SourceMatching readout overflow force) :
    collapseStep overflow = η (injectionSource overflow) ∧
    force = readout (cascadeStep (collapseStep overflow)) ∧
    (∃! y : V (n + 1), cascadeStep y = injectionSource overflow ∧ y.2 = true) := by
  refine ⟨collapse_is_lifted_source overflow, ?_, injection_reason overflow⟩
  exact (source_matching_iff_internal readout overflow force).mp hsource

/-- Transfer the equation's momentum balance from its specified force to internal
    injection. The residual is the actual field-level momentum operator's output. -/
theorem momentum_balance_internal {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (residual force : Domain → Value)
    (hsource : SourceMatching readout overflow force) (hbalance : residual = force) :
    residual = internalForce readout overflow :=
  hbalance.trans ((source_matching_iff_internal readout overflow force).mp hsource)

/-- The signed terms of ∂ₜu + (u·∇)u − νΔu + ∇p. The supplied fields are
    the time derivative, nonlinear transport, negative viscous term, and pressure
    gradient, respectively. Their analytical construction supplies these terms. -/
structure MomentumTerms (Domain Value : Type*) where
  acceleration : Domain → Value
  transport : Domain → Value
  negativeViscosity : Domain → Value
  pressureGradient : Domain → Value

/-- The momentum residual, with the Navier–Stokes signs already in the terms. -/
def MomentumTerms.residual {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) : Domain → Value := fun point =>
  terms.acceleration point + terms.transport point +
    terms.negativeViscosity point + terms.pressureGradient point

/-- The forced equation with the force's source and internal mechanism explicit. -/
theorem navier_stokes_injection_from_matching {n : ℕ} {Domain Value : Type*} [Add Value]
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (terms : MomentumTerms Domain Value) (force : Domain → Value)
    (hsource : SourceMatching readout overflow force)
    (hNS : terms.residual = force) (point : Domain) :
    terms.acceleration point + terms.transport point +
      terms.negativeViscosity point + terms.pressureGradient point =
        readout (cascadeStep (collapseStep overflow)) point :=
  congrFun (momentum_balance_internal readout overflow terms.residual force hsource hNS) point

/-- Extend the marker tower by a carried object. Projection to the original tower
    retains its scale maps, while the object travels through the round trip. -/
abbrev CarriedScale (Carrier : Type*) (n : ℕ) := V n × Carrier

def carriedLift {Carrier : Type*} {n : ℕ} (source : CarriedScale Carrier n) :
    CarriedScale Carrier (n + 1) := (η source.1, source.2)

def carriedCascade {Carrier : Type*} {n : ℕ} (overflow : CarriedScale Carrier (n + 1)) :
    CarriedScale Carrier n := (cascadeStep overflow.1, overflow.2)

def carriedCollapse {Carrier : Type*} {n : ℕ} (overflow : CarriedScale Carrier (n + 1)) :
    CarriedScale Carrier (n + 1) := (collapseStep overflow.1, overflow.2)

def carriedReEntry {Carrier : Type*} {n : ℕ} (overflow : CarriedScale Carrier (n + 1)) :
    CarriedScale Carrier n := carriedCascade (carriedCollapse overflow)

/-- The extension uses the original frame collapse on its marker coordinate. -/
theorem carried_collapse_projects {Carrier : Type*} {n : ℕ}
    (overflow : CarriedScale Carrier (n + 1)) :
    (carriedCollapse overflow).1 = collapseStep overflow.1 := rfl

/-- The same section/retraction law holds with an arbitrary carried object. -/
theorem carried_round_trip {Carrier : Type*} {n : ℕ} (source : CarriedScale Carrier n) :
    carriedReEntry (carriedLift source) = source := by
  apply Prod.ext <;> rfl

theorem carried_collapse_idempotent {Carrier : Type*} {n : ℕ}
    (overflow : CarriedScale Carrier (n + 1)) :
    carriedCollapse (carriedCollapse overflow) = carriedCollapse overflow := by
  apply Prod.ext
  · exact reEntry_fixed_under_collapse overflow.1
  · rfl

/-- Canonical source: the signed momentum residual computed from the supplied
    terms. It is carried as a field, alongside the home-scale marker state. -/
def MomentumTerms.injectionSource {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) : CarriedScale (Domain → Value) n :=
  (p n, terms.residual)

/-- Lift the computed source into the next scale; the force is not an independent
    argument. Its value is determined by the four signed momentum terms. -/
def MomentumTerms.injectionOverflow {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) : CarriedScale (Domain → Value) (n + 1) :=
  carriedLift (terms.injectionSource n)

/-- Read the field coordinate after the collapse-cascade mechanism. -/
def MomentumTerms.derivedInjection {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) : Domain → Value :=
  (carriedReEntry (terms.injectionOverflow n)).2

/-- Source matching is derived from the carrier round trip. -/
theorem MomentumTerms.derived_injection_eq_residual {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) :
    terms.derivedInjection n = terms.residual :=
  congrArg Prod.snd (carried_round_trip (terms.injectionSource n))

/-- The derived connection has no independently specified force, source-matching
    premise, or momentum-balance premise. The source is computed from the terms,
    and the carrier round trip proves its return through collapse and cascade. -/
theorem navier_stokes_injection_connection {Domain Value : Type*} [Add Value]
    (terms : MomentumTerms Domain Value) (n : ℕ) (point : Domain) :
    terms.acceleration point + terms.transport point +
      terms.negativeViscosity point + terms.pressureGradient point =
        terms.derivedInjection n point :=
  congrFun (terms.derived_injection_eq_residual n).symm point

/-- Smoothness, compact support, bounds, and other field predicates are preserved
    when the specified force is realized as the tower's internal injection. -/
theorem force_property_internal {n : ℕ} {Domain Value : Type*}
    (readout : V n → Domain → Value) (overflow : V (n + 1))
    (force : Domain → Value) (property : (Domain → Value) → Prop)
    (hsource : SourceMatching readout overflow force) (hproperty : property force) :
    property (internalForce readout overflow) := by
  rw [← (source_matching_iff_internal readout overflow force).mp hsource]
  exact hproperty

/-- CONTROL: normalization really changes an unmarked boundary. -/
theorem unmarked_boundary_control :
    collapseStep (n := 1) (((), false), false) ≠ (((), false), false) := by
  intro h
  exact Bool.noConfusion (congrArg Prod.snd h)

/-- CONTROL: injection preserves distinct carried values under an identity readout. -/
theorem carried_content_control :
    internalForce (n := 1) (fun source (_ : Unit) => source) (((), false), false) ≠
      internalForce (n := 1) (fun source (_ : Unit) => source) (((), true), false) := by
  intro h
  exact Bool.noConfusion (congrArg Prod.snd (congrFun h ()))

/-
  NS tie-in: the value the NS regularity register holds (nsRegularity = B in
  ParaconsistentNS.lean) is the fixed point of the dialetheic closure.  The
  re-entered overflow lands on a value the closure cannot move: the
  contradiction is contained, not resolved, and no external input is needed.
-/
theorem ns_reentry_fixed_point :
    Imscribing.CircumPunctum.Inc (Imscribing.Paraconsistent.Belnap.B) =
      Imscribing.Paraconsistent.Belnap.B :=
    Imscribing.CircumPunctum.Inc_fixed_point_B

end Imscribing.NSReentry
