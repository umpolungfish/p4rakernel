import Imscribing.Paraconsistent.SixteenThreeTrilattice
import Imscribing.Paraconsistent.DeMorganBooleanCentre
import Mathlib

/-!
# iutt.pdf: the explicitly specified mathematical construction

Source: ig-docs/iutt.pdf, read 2026-09-08. Section references below refer to
that version. Uses the existing four-lane SIXTEEN₃ carrier and FOUR adjoints.

The source uses π_cl both for erasure to FOUR and for a further two-pole
restriction. Here `eraseInformation` and `booleanShadow` distinguish them.
The filtered example proves the existential/non-implication content of
Proposition 18.1; no arithmetic height bound or IUT III Corollary 3.12 is
assumed or asserted. Lean supplies the metatheory; `Entails` below is the
explicit non-explosive object-language consequence relation.
-/
namespace Imscribing.IUTT

abbrev State := Reg16_3
def empty : State := (false, false, false, false)
def truth : State := (true, false, false, false)
def falsity : State := (false, true, false, false)
def both : State := (true, true, false, false)
def ambient : State := (false, false, true, true)
def allLanes : State := (true, true, true, true)
def boundedDiscrepancy : State := (false, true, true, true)

theorem sixteen_states : Fintype.card State = 16 := by decide

/-- Explicit set reading, in T,F,t,f order. -/
def support (x : State) : Set (Fin 4) :=
  {i | (![x.bigT, x.bigF, x.smallT, x.smallF] : Fin 4 → Bool) i = true}
theorem support_union (x y : State) : support (x.union y) = support x ∪ support y := by
  ext i
  fin_cases i <;> simp [support, Reg16_3.union, Reg16_3.mk,
    Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]

def intersect (x y : State) : State :=
  (x.bigT && y.bigT, x.bigF && y.bigF,
   x.smallT && y.smallT, x.smallF && y.smallF)
theorem support_intersection (x y : State) :
    support (intersect x y) = support x ∩ support y := by
  ext i
  fin_cases i <;> simp [support, intersect,
    Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
def positive (x : State) := intersect x (true, false, true, false)
def negative (x : State) := intersect x (false, true, false, true)
def truthPart (x : State) := intersect x truth
def infoPart (x : State) := intersect x ambient
def falsePart (x : State) := intersect x falsity

/-- Proposition 2.1, two-component decomposition. -/
theorem binary_recovery : ∀ x : State,
    (positive x).union (negative x) = x := by decide
theorem binary_disjoint : ∀ x : State,
    intersect (positive x) (negative x) = empty := by decide
/-- Proposition 2.1, displayed order T | t,f | F. -/
theorem ternary_recovery : ∀ x : State,
    ((truthPart x).union (infoPart x)).union (falsePart x) = x := by decide
theorem ternary_disjoint : ∀ x : State,
    intersect (truthPart x) (infoPart x) = empty ∧
    intersect (truthPart x) (falsePart x) = empty ∧
    intersect (infoPart x) (falsePart x) = empty := by decide
theorem polarity_involution : ∀ x : State, x.invol.invol = x :=
  Reg16_3.invol_involutive

def transport (gT gI gF : State → State) (x : State) : State :=
  ((gT (truthPart x)).union (gI (infoPart x))).union (gF (falsePart x))
theorem identity_transport (x : State) : transport id id id x = x :=
  ternary_recovery x
theorem theta_terminal : (truth.union ambient).union falsity = allLanes := by decide
theorem discrepancy_terminal : (empty.union ambient).union falsity = boundedDiscrepancy := by
  decide
theorem unequal_branches_recover : truth ≠ ambient ∧ ambient ≠ falsity ∧
    (truth.union ambient).union falsity = allLanes := by decide

/-- Sections 5, 12, 16: this erasure lands in FOUR, not in two poles. -/
def eraseInformation (x : State) : State := intersect x both
theorem erasure_idempotent : ∀ x : State,
    eraseInformation (eraseInformation x) = eraseInformation x := by decide
theorem erasure_fixed_iff : ∀ x : State,
    eraseInformation x = x ↔ x.smallT = false ∧ x.smallF = false := by decide
theorem theta_shadow : eraseInformation allLanes = both := by decide
theorem discrepancy_shadow : eraseInformation boundedDiscrepancy = falsity := by decide
theorem four_preimages_of_falsity :
    eraseInformation falsity = falsity ∧
    eraseInformation (false, true, true, false) = falsity ∧
    eraseInformation (false, true, false, true) = falsity ∧
    eraseInformation boundedDiscrepancy = falsity := by decide
theorem erasure_not_injective : ¬ Function.Injective eraseInformation := by
  intro h
  have bad := h (show eraseInformation falsity = eraseInformation boundedDiscrepancy by decide)
  exact (by decide : falsity ≠ boundedDiscrepancy) bad
theorem no_erasure_decoder : ¬ ∃ decode : State → State,
    ∀ x, decode (eraseInformation x) = x := by
  rintro ⟨decode, h⟩
  apply erasure_not_injective
  intro x y e
  calc x = decode (eraseInformation x) := (h x).symm
       _ = decode (eraseInformation y) := congrArg decode e
       _ = y := h y

def embedFour : Belnap → State
  | .N => empty | .T => truth | .F => falsity | .B => both
def toFour (x : State) : Belnap :=
  match x.bigT, x.bigF with
  | false, false => .N | true, false => .T | false, true => .F | true, true => .B
theorem four_retraction : ∀ v : Belnap, toFour (embedFour v) = v := by
  intro v; cases v <;> rfl
theorem erasure_is_four_projection : ∀ x : State,
    embedFour (toFour x) = eraseInformation x := by decide
def booleanShadow (x : State) : Belnap := DeMorganBooleanCentre.boolSwitch (toFour x)
theorem boolean_shadow_lands_in_centre (x : State) :
    DeMorganBooleanCentre.inCentre (booleanShadow x) :=
  DeMorganBooleanCentre.boolSwitch_image_in_centre _
theorem boolean_shadow_not_injective : ¬ Function.Injective booleanShadow := by
  intro h
  exact (by decide : falsity ≠ boundedDiscrepancy)
    (h (show booleanShadow falsity = booleanShadow boundedDiscrepancy by rfl))

/-- Section 3.1: the two adjoints reuse the existing scalar proofs. -/
theorem coreflection (c x : Belnap) (hc : DeMorganBooleanCentre.inCentre c) :
    ClassicalRestriction.truthLE c x =
      ClassicalRestriction.truthLE c (DeMorganBooleanCentre.boolSwitch x) :=
  DeMorganBooleanCentre.truth_inclCentre_left_adjoint c x hc
theorem reflection (x c : Belnap) (hc : DeMorganBooleanCentre.inCentre c) :
    ClassicalRestriction.truthLE (DeMorganBooleanCentre.truthSwitch x) c =
      ClassicalRestriction.truthLE x c :=
  DeMorganBooleanCentre.truth_truthSwitch_left_adjoint x c hc
/-- Theorem 3.1, expressed with a centre-valued endomap. -/
theorem contradictory_closure_not_boolean :
    ¬ ∃ f : DeMorganBooleanCentre.BoolCentre → DeMorganBooleanCentre.BoolCentre,
      ∀ c, DeMorganBooleanCentre.inclCentre (f c) =
        ParaconsistentFrobeniusClosure.inc (DeMorganBooleanCentre.inclCentre c) := by
  rintro ⟨f, h⟩
  let c : DeMorganBooleanCentre.BoolCentre := ⟨.T, by decide⟩
  have e := h c
  rw [ParaconsistentFrobeniusClosure.inc_always_B] at e
  have hc := (f c).property
  change DeMorganBooleanCentre.inCentre (DeMorganBooleanCentre.inclCentre (f c)) at hc
  rw [e] at hc
  exact (by decide : ¬ DeMorganBooleanCentre.inCentre Belnap.B) hc

theorem information_closure_properties :
    (∀ v : Belnap, ClassicalRestriction.infoLE v (ParaconsistentFrobeniusClosure.inc v)) ∧
    (∀ v w : Belnap, ClassicalRestriction.infoLE v w →
      ClassicalRestriction.infoLE (ParaconsistentFrobeniusClosure.inc v)
        (ParaconsistentFrobeniusClosure.inc w)) ∧
    (∀ v : Belnap, ParaconsistentFrobeniusClosure.inc (ParaconsistentFrobeniusClosure.inc v) =
      ParaconsistentFrobeniusClosure.inc v) := by
  refine ⟨?_, ?_, ParaconsistentFrobeniusClosure.frobenius_closure⟩
  · intro v
    rw [ParaconsistentFrobeniusClosure.inc_always_B]
    cases v <;> rfl
  · intro v w _
    simp only [ParaconsistentFrobeniusClosure.inc_always_B]
    rfl

/-! Section 4's explicitly schematic example, not a model of the Θ-link. -/
def alienCorrespondence : ℝ ≃ ℝ where
  toFun x := x + 1
  invFun y := y - 1
  left_inv x := by ring
  right_inv y := by ring
theorem alien_not_ring_hom : ¬ ∃ f : ℝ →+* ℝ, ∀ x, f x = alienCorrespondence x := by
  rintro ⟨f, h⟩
  have bad := h 0
  simp [alienCorrespondence, map_zero] at bad

/-- Section 3: positive-support semantics, separate from Lean's Prop logic. -/
inductive Formula where
  | atom : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
def evaluate (v : Nat → State) : Formula → State
  | .atom n => v n
  | .neg p => (evaluate v p).invol
  | .conj p q => (evaluate v p).meetT (evaluate v q)
  | .disj p q => (evaluate v p).joinT (evaluate v q)
def designated (x : State) : Prop := x.bigT = true
def Entails (premises : List Formula) (q : Formula) : Prop :=
  ∀ v : Nat → State, (∀ p ∈ premises, designated (evaluate v p)) → designated (evaluate v q)
theorem non_explosion : ¬ Entails [.atom 0, .neg (.atom 0)] (.atom 1) := by
  intro h
  let v : Nat → State := fun n => if n = 0 then both else falsity
  have bad := h v (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl)
  simp [designated, evaluate, v, falsity, Reg16_3.bigT] at bad

/-- Sections 2 and 12: invariant update leaves the full state available. -/
def update {K : Type*} (Φ : State → K → K) (p : State × K) : State × K :=
  (p.1, Φ p.1 p.2)
theorem update_preserves_state {K : Type*} (Φ : State → K → K) (p : State × K) :
    (update Φ p).1 = p.1 := rfl
theorem terminal_scalar {K V : Type*} (Φ : State → K → K) (h : State × K → V) (k : K) :
    h (update Φ (boundedDiscrepancy, k)) =
      h (boundedDiscrepancy, Φ boundedDiscrepancy k) := rfl

/-! ## Section 12.2: reconnection and a separate boundary augmentation -/
abbrev Vertex := Fin 6
/-- 0 initial, 1/2/3 branches, 4 union, 5 scalar terminal. -/
def Edge (u v : Vertex) : Prop :=
  (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 3)) ∨
  ((u = 1 ∨ u = 2 ∨ u = 3) ∧ v = 4) ∨ (u = 4 ∧ v = 5)
instance (u v : Vertex) : Decidable (Edge u v) := by unfold Edge; infer_instance
abbrev Reach := Relation.ReflTransGen Edge
def Reconnects : Prop := ∃ v : Vertex, Edge 1 v ∧ Edge 2 v ∧ Edge 3 v
theorem branches_reconnect : Reconnects := ⟨4, by decide, by decide, by decide⟩
theorem finite_terminal_has_no_successor : ∀ v : Vertex, ¬ Edge 5 v := by decide
theorem finite_no_return : ¬ Reach 5 0 := by
  intro h
  rcases h.cases_head with h | ⟨v, hv, _⟩
  · exact (by decide : (5 : Vertex) ≠ 0) h
  · exact finite_terminal_has_no_successor v hv
/-- Explicit edge realization of the closing boundary, not an edge of Edge. -/
def BoundaryEdge (u v : Vertex) : Prop := Edge u v ∨ (u = 5 ∧ v = 0)
theorem boundary_return : Relation.ReflTransGen BoundaryEdge 5 0 :=
  Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl⟩)
theorem reconnection_return_triple : Reconnects ∧ ¬ Reach 5 0 ∧
    Relation.ReflTransGen BoundaryEdge 5 0 :=
  ⟨branches_reconnect, finite_no_return, boundary_return⟩

/-! ## Section 12.3: the actual C₁₂ action -/
abbrev Phase := ZMod 12
def rotate (k : Phase) : Phase := k + 1
def PhaseInvariant {V : Type*} (I : Phase → V) : Prop := ∀ k, I (rotate k) = I k
theorem phase_twelve (k : Phase) : k + (12 : Phase) = k := by
  rw [show (12 : Phase) = 0 by decide, add_zero]
theorem invariant_nat_shift {V : Type*} (I : Phase → V) (h : PhaseInvariant I)
    (k : Phase) (n : Nat) : I (k + (n : Phase)) = I k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact (h (k + (n : Phase))).trans ih
theorem phase_invariant_iff_constant {V : Type*} (I : Phase → V) :
    PhaseInvariant I ↔ ∀ k, I k = I 0 := by
  constructor
  · intro h k
    have e := invariant_nat_shift I h 0 k.val
    simpa only [zero_add, ZMod.natCast_zmod_val] using e
  · intro h k
    exact (h (rotate k)).trans (h k).symm
theorem phase_dependent_example : ¬ PhaseInvariant (id : Phase → Phase) := by
  intro h
  exact (by decide : rotate (0 : Phase) ≠ 0) (h 0)

/-! ## Sections 18–19: filtration degree and loss of positional evaluation -/
structure Filtration (α : Type*) where
  level : Nat → Set α
  monotone : Monotone level
  exhaustive : ∀ x, ∃ j, x ∈ level j
noncomputable def Filtration.degree {α : Type*} (F : Filtration α) (x : α) : Nat :=
  @Nat.find (fun j => x ∈ F.level j) (Classical.decPred _) (F.exhaustive x)
theorem Filtration.degree_mem {α : Type*} (F : Filtration α) (x : α) :
    x ∈ F.level (F.degree x) := by
  classical
  exact Nat.find_spec (F.exhaustive x)
theorem Filtration.degree_le_iff {α : Type*} (F : Filtration α) (x : α) (j : Nat) :
    F.degree x ≤ j ↔ x ∈ F.level j := by
  classical
  constructor
  · intro h; exact F.monotone h (F.degree_mem x)
  · intro h; exact Nat.find_min' (F.exhaustive x) h

/-- An evaluation distinguishing one fiber cannot factor through its erasure. -/
theorem evaluation_no_factor {α β γ : Type*} (forget : α → β) (evaluate : α → γ)
    (x y : α) (same : forget x = forget y) (different : evaluate x ≠ evaluate y) :
    ¬ ∃ h : β → γ, evaluate = h ∘ forget := by
  rintro ⟨h, e⟩
  apply different
  rw [e]
  exact congrArg h same

/-- A three-position vector packet: this example establishes the general
    filtration-loss phenomenon, not an identification with IUT log-shells. -/
abbrev Packet := Fin 3 → ℝ
def packetFiltration : Filtration Packet where
  level j := {x | ∀ i : Fin 3, j < i.val → x i = 0}
  monotone := by
    intro j k hjk x hx i hki
    exact hx i (lt_of_le_of_lt hjk hki)
  exhaustive := by
    intro x
    refine ⟨2, ?_⟩
    intro i hi
    have := i.isLt
    omega
def atOne : Packet := ![0, 1, 0]
def atTwo : Packet := ![0, 0, 1]
def blind (x : Packet) : ℝ := ∑ i : Fin 3, x i
def weighted (x : Packet) : ℝ := ∑ i : Fin 3, (i.val : ℝ)^2 * x i
theorem same_blind_value : blind atOne = 1 ∧ blind atTwo = 1 := by
  norm_num [blind, atOne, atTwo, Fin.sum_univ_succ]
theorem different_weighted_values : weighted atOne = 1 ∧ weighted atTwo = 4 := by
  norm_num [weighted, atOne, atTwo, Fin.sum_univ_succ]
theorem weighted_does_not_factor : ¬ ∃ h : ℝ → ℝ, weighted = h ∘ blind := by
  apply evaluation_no_factor blind weighted atOne atTwo
  · exact same_blind_value.1.trans same_blind_value.2.symm
  · rw [different_weighted_values.1, different_weighted_values.2]; norm_num
theorem degree_atOne : packetFiltration.degree atOne = 1 := by
  have upper : packetFiltration.degree atOne ≤ 1 := by
    rw [Filtration.degree_le_iff]
    intro i hi
    fin_cases i <;> norm_num [atOne] at *
  have lower : ¬ packetFiltration.degree atOne ≤ 0 := by
    rw [Filtration.degree_le_iff]
    intro h
    have bad := h (1 : Fin 3) (by decide)
    norm_num [atOne] at bad
  omega
theorem degree_atTwo : packetFiltration.degree atTwo = 2 := by
  have upper : packetFiltration.degree atTwo ≤ 2 := by
    rw [Filtration.degree_le_iff]
    intro i hi
    have := i.isLt
    omega
  have lower : ¬ packetFiltration.degree atTwo ≤ 1 := by
    rw [Filtration.degree_le_iff]
    intro h
    have bad := h (2 : Fin 3) (by decide)
    change (1 : ℝ) = 0 at bad
    norm_num at bad
  omega

/-- Proposition 18.1's "may": an explicit family whose blind inequality
    is always a tautology but whose filtered inequality is not. -/
def examplePacket (b : Bool) : Packet := if b then atTwo else atOne
theorem filtered_nonvacuity :
    (∀ b : Bool, blind (examplePacket b) ≤ 2) ∧
    weighted (examplePacket false) ≤ 2 ∧
    ¬ weighted (examplePacket true) ≤ 2 := by
  constructor
  · intro b; cases b <;> simp [examplePacket, same_blind_value.1, same_blind_value.2]
  · norm_num [examplePacket, different_weighted_values.1, different_weighted_values.2]

/-- A genuine tensor-product realization of the finite example, transported
    along the standard left-unit linear equivalence. -/
abbrev TensorPacket := TensorProduct ℝ ℝ Packet
noncomputable def unpackTensor : TensorPacket ≃ₗ[ℝ] Packet := TensorProduct.lid ℝ Packet
noncomputable def tensorFiltration : Filtration TensorPacket where
  level j := {t | unpackTensor t ∈ packetFiltration.level j}
  monotone := by
    intro j k hjk t ht
    exact packetFiltration.monotone hjk ht
  exhaustive t := packetFiltration.exhaustive (unpackTensor t)
noncomputable def tensorAtOne : TensorPacket := unpackTensor.symm atOne
noncomputable def tensorAtTwo : TensorPacket := unpackTensor.symm atTwo
noncomputable def tensorBlind (t : TensorPacket) : ℝ := blind (unpackTensor t)
noncomputable def tensorWeighted (t : TensorPacket) : ℝ := weighted (unpackTensor t)
theorem tensor_same_shadow : tensorBlind tensorAtOne = tensorBlind tensorAtTwo := by
  simp [tensorBlind, tensorAtOne, tensorAtTwo, same_blind_value.1, same_blind_value.2]
theorem tensor_different_weights : tensorWeighted tensorAtOne ≠ tensorWeighted tensorAtTwo := by
  norm_num [tensorWeighted, tensorAtOne, tensorAtTwo,
    different_weighted_values.1, different_weighted_values.2]
theorem tensor_weighted_no_factor : ¬ ∃ h : ℝ → ℝ, tensorWeighted = h ∘ tensorBlind :=
  evaluation_no_factor tensorBlind tensorWeighted tensorAtOne tensorAtTwo
    tensor_same_shadow tensor_different_weights
theorem tensor_degree_agrees (t : TensorPacket) :
    tensorFiltration.degree t = packetFiltration.degree (unpackTensor t) := by
  apply Nat.le_antisymm
  · rw [Filtration.degree_le_iff]
    exact packetFiltration.degree_mem (unpackTensor t)
  · rw [Filtration.degree_le_iff]
    exact tensorFiltration.degree_mem t
theorem tensor_positions : tensorFiltration.degree tensorAtOne = 1 ∧
    tensorFiltration.degree tensorAtTwo = 2 := by
  simp [tensor_degree_agrees, tensorAtOne, tensorAtTwo, degree_atOne, degree_atTwo]

end Imscribing.IUTT
