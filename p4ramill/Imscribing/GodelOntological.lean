/-
  Imscribing/GodelOntological.lean
  Gödel's ontological argument, completed: Ax1–Ax5, Df1–Df3, Th1–Th4, every
  theorem closed sans sorry.

  The argument is higher-order modal S5. This is a shallow embedding: a modal
  proposition is a truth value indexed by a world, `w → Prop`; the connectives
  act pointwise; `box` reads a proposition at every accessible world and `dia`
  at some accessible world. A property is `i → w → Prop`, an individual carried
  to a world-indexed truth. Positiveness `P` is itself world-indexed, as in
  Gödel: what counts as a positive property may vary by world.

  The frame is S5: accessibility is reflexive, symmetric and transitive. The
  final theorem is the one that needs the full strength. Th4 lifts `◇□∃x G(x)`
  to `□∃x G(x)`, and that lift is exactly where symmetry and transitivity of
  accessibility are spent. Reflexivity is carried for the S5 frame; the chain
  does not spend it, which states plainly what the proof costs.

  The known feature of this argument is modal collapse: everything true is
  necessarily true. That is not patched here. It is the Frobenius fixed point
  read in modal dress, the same μ∘δ = id closure the kernel states elsewhere:
  once the God-like essence necessitates its own instantiation, the accessible
  worlds fuse and the split back is the identity.
-/
import Mathlib.Tactic

namespace Imscribing.GodelOntological

universe u v

variable {i : Type u}   -- individuals
variable {w : Type v}   -- worlds

/-- A modal proposition: a truth value at each world. -/
abbrev MProp (w : Type v) := w → Prop

/-- Pointwise negation. -/
def mnot (p : MProp w) : MProp w := fun x => ¬ p x

/-- Pointwise conjunction. -/
def mand (p q : MProp w) : MProp w := fun x => p x ∧ q x

/-- Pointwise implication. -/
def mimp (p q : MProp w) : MProp w := fun x => p x → q x

/-- Pointwise biconditional. -/
def miff (p q : MProp w) : MProp w := fun x => p x ↔ q x

/-- Necessity: true at every accessible world. -/
def box (r : w → w → Prop) (p : MProp w) : MProp w := fun x => ∀ y, r x y → p y

/-- Possibility: true at some accessible world. -/
def dia (r : w → w → Prop) (p : MProp w) : MProp w := fun x => ∃ y, r x y ∧ p y

/-- A modal proposition holds as a theorem when it holds at every world. -/
def valid (p : MProp w) : Prop := ∀ x, p x

section Argument

variable (r : w → w → Prop)
-- Positiveness of a property, world-indexed.
variable (P : (i → MProp w) → MProp w)

/-- Df.1  God-like: an individual bearing every positive property. -/
def God (x : i) : MProp w := fun world => ∀ φ : i → MProp w, P φ world → φ x world

/-- Df.2  Essence: φ holds of x and necessitates every property x has.
    Positiveness plays no role in the definition, so `ess` takes only the frame. -/
def ess (φ : i → MProp w) (x : i) : MProp w :=
  fun world => φ x world ∧
    ∀ ψ : i → MProp w, ψ x world → box r (fun v => ∀ y, φ y v → ψ y v) world

/-- Df.3  Necessary existence: every essence of x is necessarily instantiated. -/
def NE (x : i) : MProp w :=
  fun world => ∀ φ : i → MProp w, ess r φ x world → box r (fun v => ∃ y, φ y v) world

-- The five axioms, each stated as valid (holding at every world).

/-- Ax.1  A positive property necessarily entailing ψ makes ψ positive. -/
def Ax1 : Prop :=
  ∀ φ ψ : i → MProp w,
    valid (mimp (mand (P φ) (box r (fun v => ∀ x, φ x v → ψ x v))) (P ψ))

/-- Ax.2  Exactly one of a property and its negation is positive. -/
def Ax2 : Prop :=
  ∀ φ : i → MProp w, valid (miff (P (fun x => mnot (φ x))) (mnot (P φ)))

/-- Ax.3  Being God-like is positive. -/
def Ax3 : Prop := valid (P (God P))

/-- Ax.4  Positiveness is necessary. -/
def Ax4 : Prop := ∀ φ : i → MProp w, valid (mimp (P φ) (box r (P φ)))

/-- Ax.5  Necessary existence is positive. -/
def Ax5 : Prop := valid (P (NE r))

/-- Th.1  Every positive property is possibly instantiated.

    If it were not, then at this world it is necessarily empty, so it
    necessarily entails every property vacuously. Ax.1 then makes every
    property positive, including the negation of φ, and Ax.2 turns that into
    φ not being positive, against the hypothesis. -/
theorem th1 (h1 : Ax1 r P) (h2 : Ax2 P) (φ : i → MProp w) :
    valid (mimp (P φ) (dia r (fun v => ∃ x, φ x v))) := by
  intro world hPφ
  by_contra hcon
  -- hcon : ¬ ∃ v, r world v ∧ ∃ x, φ x v
  have hempty : box r (fun v => ∀ x, φ x v → (mnot (φ x)) v) world := by
    intro y hry x hφxy
    exact absurd ⟨y, hry, ⟨x, hφxy⟩⟩ hcon
  -- Ax.1 with ψ = ¬φ gives P(¬φ) at this world.
  have hPnegφ : P (fun x => mnot (φ x)) world :=
    h1 φ (fun x => mnot (φ x)) world ⟨hPφ, hempty⟩
  -- Ax.2 turns P(¬φ) into ¬P(φ).
  exact (h2 φ world).mp hPnegφ hPφ

/-- Th.2  It is possible that a God-like individual exists. -/
theorem th2 (h1 : Ax1 r P) (h2 : Ax2 P) (h3 : Ax3 P) :
    valid (dia r (fun v => ∃ x, God P x v)) := by
  intro world
  exact th1 r P h1 h2 (God P) world (h3 world)

/-- Th.3  A God-like individual has being God-like as its essence.

    Any property ψ that x has must be positive: were it not, its negation would
    be positive by Ax.2, and the God-like x would then bear the negation,
    contradicting that x has ψ. A positive property is necessary by Ax.4, and a
    necessarily positive property is necessarily borne by every God-like being,
    which is the essence condition. -/
theorem th3 (h2 : Ax2 P) (h4 : Ax4 r P) (x : i) :
    valid (mimp (God P x) (ess r (God P) x)) := by
  intro world hGx
  refine ⟨hGx, ?_⟩
  intro ψ hψx
  -- ψ is positive at this world.
  have hPψ : P ψ world := by
    by_contra hnot
    have hPnegψ : P (fun z => mnot (ψ z)) world := (h2 ψ world).mpr hnot
    have : (mnot (ψ x)) world := hGx (fun z => mnot (ψ z)) hPnegψ
    exact this hψx
  -- Ax.4: positiveness is necessary; unfold the necessity into the entailment.
  have hbox : box r (P ψ) world := h4 ψ world hPψ
  intro v hrv y hGyv
  exact hGyv ψ (hbox v hrv)

/-- Th.4  Necessarily a God-like individual exists.

    Where a God-like x sits, x has necessary existence (Ax.5, since x bears
    every positive property), and its essence (Th.3) is therefore necessarily
    instantiated, so `□∃x G(x)` holds there. Th.2 places such a world one step
    away, giving `◇□∃x G(x)`. Symmetry and transitivity of accessibility then
    lift that to `□∃x G(x)` outright. -/
theorem th4
    (h1 : Ax1 r P) (h2 : Ax2 P) (h3 : Ax3 P) (h4 : Ax4 r P) (h5 : Ax5 r P)
    (hsymm : Symmetric r) (htrans : Transitive r) :
    valid (box r (fun v => ∃ x, God P x v)) := by
  -- Abbreviate the target proposition A = ∃x G(x).
  set A : MProp w := fun v => ∃ x, God P x v with hA
  -- Local lemma: where A holds, □A holds — via necessary existence and essence.
  have hL : ∀ world, A world → box r A world := by
    intro world hAw
    obtain ⟨x, hGx⟩ := hAw
    -- x bears necessary existence, since NE is positive (Ax.5) and x is God-like.
    have hNEx : NE r x world := hGx (NE r) (h5 world)
    -- x's essence is being God-like (Th.3), which NE necessitates as instantiated.
    have hEss : ess r (God P) x world := th3 r P h2 h4 x world hGx
    exact hNEx (God P) hEss
  -- Th.2 gives ◇A everywhere; through hL that is ◇□A.
  intro world
  obtain ⟨v, hrwv, hAv⟩ := th2 r P h1 h2 h3 world
  have hboxAv : box r A v := hL v hAv
  -- S5 lift ◇□A → □A: for any t accessible from world, symmetry+transitivity
  -- put t accessible from v, where □A already holds.
  intro t hrwt
  exact hboxAv t (htrans (hsymm hrwv) hrwt)

end Argument

/-- Consistency of the premises. Th4 is an implication from Ax1..Ax5, so it
    would be empty if those five could not hold together. They can: one world,
    one individual, and "positive" read as "held by that individual" satisfies
    all five at once. This is a model, so the axiom set is satisfiable and Th4 is
    not vacuously true over contradictory hypotheses. -/
theorem axioms_consistent :
    ∃ (r : Unit → Unit → Prop) (P : (Unit → MProp Unit) → MProp Unit),
      Ax1 r P ∧ Ax2 P ∧ Ax3 P ∧ Ax4 r P ∧ Ax5 r P := by
  refine ⟨fun _ _ => True, fun φ world => φ () world, ?_, ?_, ?_, ?_, ?_⟩
  · -- Ax1: a positive property that entails ψ everywhere hands ψ its value here.
    intro φ ψ world h
    exact h.2 world trivial () h.1
  · -- Ax2: ¬φ held by the individual iff φ is not, definitionally.
    intro φ world; exact Iff.rfl
  · -- Ax3: God-like collects the positives, and each positive is self-entailing.
    intro world φ h; exact h
  · -- Ax4: one world, so necessity of positiveness is positiveness itself.
    intro φ world hPφ y _
    have hy : y = world := Subsingleton.elim y world
    subst hy; exact hPφ
  · -- Ax5: an essence is instantiated by the individual that carries it.
    intro world φ hess z _
    have hz : z = world := Subsingleton.elim z world
    subst hz; exact ⟨(), hess.1⟩

-- Dependency audit: each theorem rests only on Lean's standard axioms
-- (propext, Classical.choice, Quot.sound). No sorryAx, no extra axiom.
#print axioms th1
#print axioms th2
#print axioms th3
#print axioms th4
#print axioms axioms_consistent

end Imscribing.GodelOntological
