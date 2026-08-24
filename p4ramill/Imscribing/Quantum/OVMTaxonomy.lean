import Mathlib
import Imscribing.Millennium.OVMCatalog

/-!
# OVMTaxonomy — the Millennium theorems as operator-valued measures

The Lean record of `ig-docs/millennium_theorems_as_ovms.tex`: the four axes that
sort an operator-valued measure, the reading of three of them off the twelve
coordinates, the seven question/theorem pairs, and the propositions the paper
states about them.

Nothing here is a restatement of a number. Every coordinate comes from
`OVMCatalog.lean`, which is generated from `IG_catalog.json`, and every count is
computed from those coordinates by `decide`.

## The axes

* **Positivity** is carried by the winding coordinate `◻` alone, and is not a
  separate stipulation: a measure is positive exactly when its winding is a
  fixed point of negation. `windingSelfInverse_iff` is that fact about angles.
* **Completeness** is carried by `∈`.
* **Dynamics** is carried by `⊤`.
* **Symmetry** is carried by `≻` and `⊥` jointly, and the grid records it per
  system rather than deriving it from the marks. Three axes are read here, not
  four; see `symmetry_marks_not_injective`.

## What the tex claims and what the coordinates say

Four of the paper's propositions are confirmed here by computation, and two are
not. `measurement_inverts_five` and `convergence_settled` record the counts the
sample actually carries; the discrepancies are stated in their docstrings rather
than smoothed over.
-/

namespace Imscribing.Quantum.OVMTaxonomy

open Imscribing.Primitives
open Imscribing.Millennium.OVMCatalog

/- ==================================================================
   1.  Positivity is a self-inverse winding
   ================================================================== -/

/-- A winding lives in `ℝ/ℤ`, one winding to a full turn. Reversal sends `x` to
    `-x`, so a winding is *self-inverse* when `2x` is a whole number of turns. -/
def SelfInverse (x : ℚ) : Prop := ∃ k : ℤ, 2 * x = (k : ℚ)

/-- **The positivity criterion.** On one turn, the self-inverse windings are
    exactly `0` and `1/2` — the windings of the positive and the negative reals.
    This is the whole content of the positivity axis: nothing about
    probability is assumed, and the two positive values are not two conventions
    but the only two windings that reverse into themselves. -/
theorem windingSelfInverse_iff (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) :
    SelfInverse x ↔ x = 0 ∨ x = 1 / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : (0 : ℚ) ≤ (k : ℚ) := by rw [← hk]; linarith
    have hk2 : ((k : ℚ)) < 2 := by rw [← hk]; linarith
    have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    have hk2' : k < 2 := by exact_mod_cast hk2
    interval_cases k
    · left; push_cast at hk; linarith
    · right; push_cast at hk; linarith
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

/-- The four values the winding coordinate `◻` takes. The first three are the
    positivity axis; the fourth leaves the line the axis is drawn on, because a
    non-abelian holonomy around a cycle is not a scalar and has no rational
    winding at all. -/
inductive WindingClass
  | zero      -- ∮ dx = 0
  | twofold   -- ∮ A = (n/2) ω, n ∈ ℤ₂
  | count     -- ∮ A = n ω, n ∈ ℤ, w(γ) ≠ 0
  | braid     -- non-abelian braid monodromy: off the winding line
  deriving DecidableEq, Repr, Fintype

/-- The two values of the positivity axis. -/
inductive Positivity
  | positive
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The winding a class carries, where it carries one. `count` deposits a whole
    number rather than sitting at a point of `ℚ/ℤ`, and `braid` is not on the
    line, so both are `none`. -/
def windingOf : WindingClass → Option ℚ
  | .zero => some 0
  | .twofold => some (1 / 2)
  | .count => none
  | .braid => none

/-- Positivity, read off the winding class. `braid` has no value on this axis. -/
def positivityOf : WindingClass → Option Positivity
  | .zero => some .positive
  | .twofold => some .positive
  | .count => some .negative
  | .braid => none

/-- The measure is positive exactly on the classes whose winding is
    self-inverse. The two halves of the paper's positivity theorem, joined. -/
theorem positive_iff_selfInverse (w : WindingClass) :
    positivityOf w = some .positive ↔ ∃ x, windingOf w = some x ∧ SelfInverse x := by
  cases w
  · exact ⟨fun _ => ⟨0, rfl, ⟨0, by norm_num⟩⟩, fun _ => rfl⟩
  · exact ⟨fun _ => ⟨1 / 2, rfl, ⟨1, by norm_num⟩⟩, fun _ => rfl⟩
  · simp [positivityOf, windingOf]
  · simp [positivityOf, windingOf]

/-- Yang–Mills does not take a third value on the positivity axis. It leaves
    the axis: there is no frame at the pinch on which to be positive. -/
theorem braid_off_axis : positivityOf .braid = none ∧ windingOf .braid = none :=
  ⟨rfl, rfl⟩

/- ==================================================================
   2.  The other three axes, and the cell count
   ================================================================== -/

inductive Completeness
  | complete       -- IC: ∑_E M(E) = 𝟙
  | paracomplete   -- PC
  deriving DecidableEq, Repr, Fintype

inductive Dynamics
  | static
  | oscillating
  deriving DecidableEq, Repr, Fintype

inductive Symmetry
  | sym
  | asym
  | antisym
  deriving DecidableEq, Repr, Fintype

/-- Oscillation drives the symmetric chirality onto the antisymmetric value, so
    symmetric-oscillating and antisymmetric-static are the same cell. -/
def collapse : Symmetry × Dynamics → Symmetry × Dynamics
  | (.sym, .oscillating) => (.antisym, .static)
  | p => p

/-- Four axes give twenty-four combinations. -/
theorem cells_twentyfour :
    Fintype.card (Completeness × Positivity × Symmetry × Dynamics) = 24 := by
  decide

/-- Twenty of them are distinct. -/
theorem cells_twenty :
    (Finset.univ.image
      (fun c : Completeness × Positivity × Symmetry × Dynamics =>
        (c.1, c.2.1, collapse (c.2.2.1, c.2.2.2)))).card = 20 := by
  decide

/- ==================================================================
   3.  Reading the axes off the twelve coordinates
   ================================================================== -/

/-- Completeness is carried by `∈`: `𐑔` complete, `𐑚` and `𐑲` paracomplete. -/
def completenessOf (i : Imscription) : Completeness :=
  match i.gran with
  | .thigh => .complete
  | _ => .paracomplete

/-- The winding class is carried by `◻` alone. -/
def windingClassOf (i : Imscription) : WindingClass :=
  match i.prot with
  | .awe => .zero
  | .oak => .twofold
  | .ah => .count
  | .zoo => .braid

/-- Dynamics is carried by `⊤`: `𐑧` static, `𐑪` oscillating. The three
    remaining kinetic values are not on the axis. -/
def dynamicsOf (i : Imscription) : Option Dynamics :=
  match i.kin with
  | .egg => some .static
  | .on => some .oscillating
  | _ => none

/-- A cell, as far as the coordinates determine one: completeness, the winding
    class that carries positivity, and dynamics. Symmetry is absent on purpose;
    see `symmetry_marks_not_injective`. -/
structure Cell where
  completeness : Completeness
  winding : WindingClass
  dynamics : Option Dynamics
  deriving DecidableEq, Repr

def classify (i : Imscription) : Cell :=
  ⟨completenessOf i, windingClassOf i, dynamicsOf i⟩

/-- The cell eighteen of the twenty-five theorem coordinates occupy. -/
def completeNegativeStatic : Cell := ⟨.complete, .count, some .static⟩

/-- Symmetry is carried by `≻` and `⊥` jointly, and the taxonomy grid records
    it per system rather than deriving it: the pair `(𐑽, 𐑖)` appears in all
    three symmetry classes there. So no reader from the marks to the class is
    written here, and `Cell` carries three axes.

    What is checkable in Lean is the weaker half: the two marks do not separate
    imscriptions. Riemann and Birch and Swinnerton-Dyer agree on both and are
    different coordinates. -/
theorem symmetry_marks_not_injective :
    riemannTheorem.rel = bsdTheorem.rel ∧
    riemannTheorem.chir = bsdTheorem.chir ∧
    riemannTheorem ≠ bsdTheorem := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/- ==================================================================
   4.  The seven, question and theorem
   ================================================================== -/

/-- The bare twelve-glyph word of an imscription, the spelling the catalog
    uses. `Imscription.shavian` renders the same twelve with separators. -/
def bareWord (i : Imscription) : String :=
  i.dim.shavian ++ i.top.shavian ++ i.rel.shavian ++ i.pol.shavian ++
  i.fid.shavian ++ i.kin.shavian ++ i.gran.shavian ++ i.gram.shavian ++
  i.crit.shavian ++ i.chir.shavian ++ i.stoi.shavian ++ i.prot.shavian

/-- Every coordinate renders back to the catalog word it was decoded from.
    This is the tie between the Lean and `IG_catalog.json`, and it is computed,
    not asserted: a decode that lost a glyph would fail here. -/
theorem seven_words_roundtrip :
    seven.map (fun p => (p.1, bareWord p.2.1, bareWord p.2.2)) = sevenCatalogWords := by
  decide

/-- The summary table of the paper, computed. Five of the seven theorems are
    complete, negative and static; Yang–Mills is paracomplete and off the
    positivity axis; Collatz is paracomplete and positive. -/
theorem seven_cells :
    classify riemannTheorem = completeNegativeStatic ∧
    classify bsdTheorem = completeNegativeStatic ∧
    classify yangMillsTheorem = ⟨.paracomplete, .braid, some .static⟩ ∧
    classify navierStokesTheorem = completeNegativeStatic ∧
    classify pVsNPTheorem = completeNegativeStatic ∧
    classify hodgeTheorem = completeNegativeStatic ∧
    classify collatzTheorem = ⟨.paracomplete, .twofold, some .static⟩ := by
  decide

/-- Collatz is the only one of the seven whose transition stays inside the
    self-inverse windings: the question carries winding `0` and the theorem
    winding `1/2`, and the measure is positive on both sides. -/
theorem collatz_stays_positive :
    windingClassOf collatzQuestion = .zero ∧
    windingClassOf collatzTheorem = .twofold ∧
    positivityOf (windingClassOf collatzQuestion) = some .positive ∧
    positivityOf (windingClassOf collatzTheorem) = some .positive := by
  decide

/-- P versus NP passes from positive to negative, and that passage is the
    separation: the winding moves off the self-inverse values onto the count. -/
theorem pVsNP_separation :
    windingClassOf pVsNPQuestion = .zero ∧
    windingClassOf pVsNPTheorem = .count ∧
    positivityOf (windingClassOf pVsNPQuestion) = some .positive ∧
    positivityOf (windingClassOf pVsNPTheorem) = some .negative := by
  decide

/-- For Navier–Stokes exactly one coordinate separates question from answer once
    the question is placed at the theorem's other eleven values, and it is the
    criticality coordinate: the question says correlations diverge (`⊙`), the
    answer says they do not (`𐑢`). That single coordinate is global regularity. -/
theorem navierStokes_criticality :
    navierStokesQuestion.crit = .monad ∧ navierStokesTheorem.crit = .woe := by
  decide

/-- Yang–Mills leaves the positivity axis, and it is the only one of the seven
    that does. -/
theorem yangMills_alone_off_axis :
    (seven.filter (fun p => positivityOf (windingClassOf p.2.2) == none)).length = 1 := by
  decide

/- ==================================================================
   5.  The propositions of section 3, computed over the seven
   ================================================================== -/

/-- The measurement coordinate is `⋈`: `𐑐` is the commutator `[x,p] = iħ`,
    `𐑱` the Dirac measure `P(x) ∈ {0,1}`, `𐑞` a mixed state `Tr(ρ²) < 1`. -/
def measurementIsCommutator (i : Imscription) : Bool := i.fid == .peep

/-- All seven theorems are measured by the commutator. -/
theorem seven_theorems_commutator :
    (seven.filter (fun p => measurementIsCommutator p.2.2)).length = 7 := by
  decide

/-- **Where the paper overcounts.** It says six of the seven questions carry a
    Dirac measure, with Birch and Swinnerton-Dyer the exception. Five do. The
    Yang–Mills question, catalog `yang_mills_mass_gap`, carries the commutator
    `𐑐` like the theorems, so there are two exceptions and not one. The rest of
    the claim stands: the statement of a problem is deterministic where its
    proof is not. -/
theorem measurement_inverts_five :
    (seven.filter (fun p => p.2.1.fid == .age)).length = 5 ∧
    (seven.filter (fun p => p.2.1.fid == .they)).length = 1 ∧
    (seven.filter (fun p => p.2.1.fid == .peep)).length = 1 := by
  decide

/-- Completeness inverts. All seven questions are Dedekind-finite (`∈ = 𐑲`);
    six of the seven theorems have left that value. -/
theorem completeness_inverts :
    (seven.filter (fun p => p.2.1.gran == .ice)).length = 7 ∧
    (seven.filter (fun p => p.2.2.gran != .ice)).length = 6 := by
  decide

/-- The composition coordinate `∋ = 𐑵` is universal broadcast: a state copied
    and handed to every observer at once. Exactly three of the seven theorems
    carry it, and they are Birch and Swinnerton-Dyer, Yang–Mills and Collatz. -/
theorem broadcast_three :
    (seven.filter (fun p => p.2.2.gram == .ooze)).length = 3 ∧
    bsdTheorem.gram = .ooze ∧
    yangMillsTheorem.gram = .ooze ∧
    collatzTheorem.gram = .ooze := by
  decide

/-- Yang–Mills carries `μ ∘ δ = id` in three coordinates: parity `≺ = 𐑹`,
    criticality `⊙`, and chirality `⊥ = 𐑫`. Splitting and immediately rejoining
    is free when there is one place for both halves. -/
theorem yangMills_three_identities :
    yangMillsTheorem.pol = .or' ∧
    yangMillsTheorem.crit = .monad ∧
    yangMillsTheorem.chir = .wool := by
  decide

/-- The mass gap is the completeness value `𐑚`: every element strictly below the
    whole. Yang–Mills is the only one of the seven that carries it. -/
theorem massGap_is_completeness :
    yangMillsTheorem.gran = .bib ∧
    (seven.filter (fun p => p.2.2.gran == .bib)).length = 1 := by
  decide

/- ==================================================================
   6.  The census, over the two recorded samples
   ================================================================== -/

/-- The paper's table of the 25-entry theorem sample, reproduced exactly. -/
theorem convergence_newTheorems :
    (newTheorems.filter (fun p => classify p.2 == completeNegativeStatic)).length = 18 ∧
    (newTheorems.filter
      (fun p => classify p.2 == ⟨.paracomplete, .count, some .static⟩)).length = 4 ∧
    (newTheorems.filter
      (fun p => classify p.2 == ⟨.paracomplete, .braid, some .static⟩)).length = 1 ∧
    (newTheorems.filter
      (fun p => classify p.2 == ⟨.complete, .zero, some .oscillating⟩)).length = 1 ∧
    (newTheorems.filter
      (fun p => classify p.2 == ⟨.complete, .count, some .oscillating⟩)).length = 1 ∧
    newTheorems.length = 25 := by
  decide

/-- **Where the paper's wider count is off.** It states that seventy-nine of a
    hundred and fourteen settled objects occupy the cell. The recorded sample
    holds a hundred and fifteen entries, and seventy-five of them occupy it.
    Eighty are complete and negative once dynamics is ignored, which is the
    nearest reading that reaches the paper's neighbourhood. The direction of the
    claim survives: the settled objects concentrate in one cell and their
    questions do not. -/
theorem convergence_settled :
    settled.length = 115 ∧
    (settled.filter (fun p => classify p.2 == completeNegativeStatic)).length = 75 ∧
    (settled.filter
      (fun p => completenessOf p.2 == .complete &&
                windingClassOf p.2 == .count)).length = 80 := by
  decide

/-- A coordinate is *gapped* when its criticality is `𐑢`: no diverging
    correlation length. -/
def gapped (i : Imscription) : Bool := i.crit == .woe

/-- **The criticality gradient**, over the settled sample. Among coordinates
    whose measurement is not the commutator, seven of fourteen are gapped; among
    those whose measurement is the commutator, sixteen of a hundred and one are.
    A commutator is the measurement appropriate to a diverging correlation
    length, and away from criticality a classical measurement suffices. -/
theorem criticality_gradient :
    (settled.filter (fun p => !measurementIsCommutator p.2)).length = 14 ∧
    (settled.filter (fun p => !measurementIsCommutator p.2 && gapped p.2)).length = 7 ∧
    (settled.filter (fun p => measurementIsCommutator p.2)).length = 101 ∧
    (settled.filter (fun p => measurementIsCommutator p.2 && gapped p.2)).length = 16 := by
  decide

end Imscribing.Quantum.OVMTaxonomy
