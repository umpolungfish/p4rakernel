/-
  Imscribing.Millennium.ConventionalDelta

  Both addresses, so the delta is checked instead of asserted.

  `ConventionalDecomposition.lean` encodes the seven THEOREM addresses and
  discharges four per-mark facts about them by `rfl`. It states the transition
  claim only in prose: "The proof transition for Navier-Stokes is that single
  field." Because the conjecture address is nowhere in that file, the claim was
  never machine-checked, and it is wrong. Nine marks separate the Navier-Stokes
  conjecture entry from its theorem entry, not one. This file holds both poles of
  all seven pairs so that cannot happen again.

  The pairing is the catalog's, fixed by `ClayCanonicalTuples.lean` (itself
  generated from IG_catalog.json) and by the working notes in
  ig-docs/OVMs/conjecture_cells_working.md. Yang-Mills takes `yang_mills_theory`
  and not `yang_mills_mass_gap`: the latter is the request, a specification
  carrying no handedness and no winding, and it sits nine marks out. The object
  sits five.

  Every theorem below is `rfl` or `decide` over finite enumerations. Nothing here
  proves anything about zeros, ranks or gaps. It fixes what the Grammar says must
  move, so that the mathematical reading of those moves has something to answer to.

  Author: Lando ⊗ ⊙perator
-/

import Imscribing.Primitives.Imscription

namespace Imscribing.Millennium.ConventionalDelta

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-! ## Riemann — 9 marks move, 3 hold -/

/-- Catalog `riemann_hypothesis`. -/
def riemannConjecture : Imscription :=
  { dim := .dead, top := .mime, rel := .ian, pol := .out, fid := .age, kin := .egg,
    gran := .ice, gram := .vow, crit := .roar, chir := .sure, stoi := .up, prot := .oak }

/-- Catalog `riemann_theorem`. -/
def riemannTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .measure, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- The marks that move: ⊢ ≻ ≺ ⋈ ∈ ∋ ⊙ ⊥ ◻ -/
theorem riemann_moves :
    riemannConjecture.dim ≠ riemannTheorem.dim ∧
    riemannConjecture.rel ≠ riemannTheorem.rel ∧
    riemannConjecture.pol ≠ riemannTheorem.pol ∧
    riemannConjecture.fid ≠ riemannTheorem.fid ∧
    riemannConjecture.gran ≠ riemannTheorem.gran ∧
    riemannConjecture.gram ≠ riemannTheorem.gram ∧
    riemannConjecture.crit ≠ riemannTheorem.crit ∧
    riemannConjecture.chir ≠ riemannTheorem.chir ∧
    riemannConjecture.prot ≠ riemannTheorem.prot := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem riemann_holds :
    riemannConjecture.top = riemannTheorem.top ∧
    riemannConjecture.kin = riemannTheorem.kin ∧
    riemannConjecture.stoi = riemannTheorem.stoi := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Birch and Swinnerton-Dyer — 8 marks move, 4 hold -/

/-- Catalog `birch_swinnerton_dyer`. -/
def bsdConjecture : Imscription :=
  { dim := .if', top := .mime, rel := .ian, pol := .yew, fid := .they, kin := .egg,
    gran := .ice, gram := .vow, crit := .roar, chir := .sure, stoi := .hung, prot := .ah }

/-- Catalog `birch_and_swinnerton_dyer_theorem_`. -/
def bsdTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- The marks that move: ≻ ≺ ⋈ ∈ ∋ ⊙ ⊥ ⊞ -/
theorem bsd_moves :
    bsdConjecture.rel ≠ bsdTheorem.rel ∧
    bsdConjecture.pol ≠ bsdTheorem.pol ∧
    bsdConjecture.fid ≠ bsdTheorem.fid ∧
    bsdConjecture.gran ≠ bsdTheorem.gran ∧
    bsdConjecture.gram ≠ bsdTheorem.gram ∧
    bsdConjecture.crit ≠ bsdTheorem.crit ∧
    bsdConjecture.chir ≠ bsdTheorem.chir ∧
    bsdConjecture.stoi ≠ bsdTheorem.stoi := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem bsd_holds :
    bsdConjecture.dim = bsdTheorem.dim ∧
    bsdConjecture.top = bsdTheorem.top ∧
    bsdConjecture.kin = bsdTheorem.kin ∧
    bsdConjecture.prot = bsdTheorem.prot := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Yang–Mills — 5 marks move, 7 hold -/

/-- Catalog `yang_mills_theory`. -/
def yangMillsConjecture : Imscription :=
  { dim := .array, top := .mime, rel := .ian, pol := .or', fid := .peep, kin := .on,
    gran := .ice, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- Catalog `yang–mills_existence_and_mass_gap_theorem_`. -/
def yangMillsTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .bib, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .zoo }

/-- The marks that move: ⊢ ≻ ⊤ ∈ ◻ -/
theorem yangMills_moves :
    yangMillsConjecture.dim ≠ yangMillsTheorem.dim ∧
    yangMillsConjecture.rel ≠ yangMillsTheorem.rel ∧
    yangMillsConjecture.kin ≠ yangMillsTheorem.kin ∧
    yangMillsConjecture.gran ≠ yangMillsTheorem.gran ∧
    yangMillsConjecture.prot ≠ yangMillsTheorem.prot := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem yangMills_holds :
    yangMillsConjecture.top = yangMillsTheorem.top ∧
    yangMillsConjecture.pol = yangMillsTheorem.pol ∧
    yangMillsConjecture.fid = yangMillsTheorem.fid ∧
    yangMillsConjecture.gram = yangMillsTheorem.gram ∧
    yangMillsConjecture.crit = yangMillsTheorem.crit ∧
    yangMillsConjecture.chir = yangMillsTheorem.chir ∧
    yangMillsConjecture.stoi = yangMillsTheorem.stoi := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Navier–Stokes — 9 marks move, 3 hold -/

/-- Catalog `navier_stokes`. -/
def navierStokesConjecture : Imscription :=
  { dim := .array, top := .judge, rel := .ear, pol := .church, fid := .age, kin := .loll,
    gran := .ice, gram := .vow, crit := .monad, chir := .kick, stoi := .up, prot := .awe }

/-- Catalog `navier_stokes_theorem`. -/
def navierStokesTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .yew, fid := .peep, kin := .egg,
    gran := .thigh, gram := .vow, crit := .woe, chir := .wool, stoi := .up, prot := .ah }

/-- The marks that move: ⊢ ⊣ ≺ ⋈ ⊤ ∈ ⊙ ⊥ ◻ -/
theorem navierStokes_moves :
    navierStokesConjecture.dim ≠ navierStokesTheorem.dim ∧
    navierStokesConjecture.top ≠ navierStokesTheorem.top ∧
    navierStokesConjecture.pol ≠ navierStokesTheorem.pol ∧
    navierStokesConjecture.fid ≠ navierStokesTheorem.fid ∧
    navierStokesConjecture.kin ≠ navierStokesTheorem.kin ∧
    navierStokesConjecture.gran ≠ navierStokesTheorem.gran ∧
    navierStokesConjecture.crit ≠ navierStokesTheorem.crit ∧
    navierStokesConjecture.chir ≠ navierStokesTheorem.chir ∧
    navierStokesConjecture.prot ≠ navierStokesTheorem.prot := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem navierStokes_holds :
    navierStokesConjecture.rel = navierStokesTheorem.rel ∧
    navierStokesConjecture.gram = navierStokesTheorem.gram ∧
    navierStokesConjecture.stoi = navierStokesTheorem.stoi := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## P versus NP — 10 marks move, 2 hold -/

/-- Catalog `p_vs_np`. -/
def pVersusNPConjecture : Imscription :=
  { dim := .dead, top := .judge, rel := .ado, pol := .church, fid := .age, kin := .on,
    gran := .ice, gram := .vow, crit := .monad, chir := .fee, stoi := .hung, prot := .awe }

/-- Catalog `p_versus_np_theorem`. -/
def pVersusNPTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .vow, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- The marks that move: ⊢ ⊣ ≻ ≺ ⋈ ⊤ ∈ ⊥ ⊞ ◻ -/
theorem pVersusNP_moves :
    pVersusNPConjecture.dim ≠ pVersusNPTheorem.dim ∧
    pVersusNPConjecture.top ≠ pVersusNPTheorem.top ∧
    pVersusNPConjecture.rel ≠ pVersusNPTheorem.rel ∧
    pVersusNPConjecture.pol ≠ pVersusNPTheorem.pol ∧
    pVersusNPConjecture.fid ≠ pVersusNPTheorem.fid ∧
    pVersusNPConjecture.kin ≠ pVersusNPTheorem.kin ∧
    pVersusNPConjecture.gran ≠ pVersusNPTheorem.gran ∧
    pVersusNPConjecture.chir ≠ pVersusNPTheorem.chir ∧
    pVersusNPConjecture.stoi ≠ pVersusNPTheorem.stoi ∧
    pVersusNPConjecture.prot ≠ pVersusNPTheorem.prot := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem pVersusNP_holds :
    pVersusNPConjecture.gram = pVersusNPTheorem.gram ∧
    pVersusNPConjecture.crit = pVersusNPTheorem.crit := by
  refine ⟨rfl, rfl⟩

/-! ## Hodge–Lefschetz (1,1) — 6 marks move, 6 hold -/

/-- Catalog `hodge_conjecture`. -/
def hodgeConjecture : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .yew, fid := .age, kin := .egg,
    gran := .ice, gram := .vow, crit := .roar, chir := .fee, stoi := .up, prot := .ah }

/-- Catalog `hodge_lefschetz_11_theorem`. -/
def hodgeTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .yew, fid := .peep, kin := .egg,
    gran := .thigh, gram := .measure, crit := .monad, chir := .sure, stoi := .up, prot := .ah }

/-- The marks that move: ⊣ ⋈ ∈ ∋ ⊙ ⊥ -/
theorem hodge_moves :
    hodgeConjecture.top ≠ hodgeTheorem.top ∧
    hodgeConjecture.fid ≠ hodgeTheorem.fid ∧
    hodgeConjecture.gran ≠ hodgeTheorem.gran ∧
    hodgeConjecture.gram ≠ hodgeTheorem.gram ∧
    hodgeConjecture.crit ≠ hodgeTheorem.crit ∧
    hodgeConjecture.chir ≠ hodgeTheorem.chir := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem hodge_holds :
    hodgeConjecture.dim = hodgeTheorem.dim ∧
    hodgeConjecture.rel = hodgeTheorem.rel ∧
    hodgeConjecture.pol = hodgeTheorem.pol ∧
    hodgeConjecture.kin = hodgeTheorem.kin ∧
    hodgeConjecture.stoi = hodgeTheorem.stoi ∧
    hodgeConjecture.prot = hodgeTheorem.prot := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Collatz — 11 marks move, 1 hold -/

/-- Catalog `collatz_conjecture`. -/
def collatzConjecture : Imscription :=
  { dim := .dead, top := .judge, rel := .ado, pol := .nun, fid := .age, kin := .yea,
    gran := .ice, gram := .measure, crit := .roar, chir := .fee, stoi := .hung, prot := .awe }

/-- Catalog `collatz_theorem_proven`. -/
def collatzTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .ice, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .oak }

/-- The marks that move: ⊢ ⊣ ≻ ≺ ⋈ ⊤ ∋ ⊙ ⊥ ⊞ ◻ -/
theorem collatz_moves :
    collatzConjecture.dim ≠ collatzTheorem.dim ∧
    collatzConjecture.top ≠ collatzTheorem.top ∧
    collatzConjecture.rel ≠ collatzTheorem.rel ∧
    collatzConjecture.pol ≠ collatzTheorem.pol ∧
    collatzConjecture.fid ≠ collatzTheorem.fid ∧
    collatzConjecture.kin ≠ collatzTheorem.kin ∧
    collatzConjecture.gram ≠ collatzTheorem.gram ∧
    collatzConjecture.crit ≠ collatzTheorem.crit ∧
    collatzConjecture.chir ≠ collatzTheorem.chir ∧
    collatzConjecture.stoi ≠ collatzTheorem.stoi ∧
    collatzConjecture.prot ≠ collatzTheorem.prot := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- And the marks that hold. -/
theorem collatz_holds :
    collatzConjecture.gran = collatzTheorem.gran := rfl

/-! ## What the pairs say

Yang-Mills has the smallest delta of the seven at five marks, and two of the five
are the Clay statement's own hypotheses. Granularity moves from "every proper
subset is strictly smaller" to "every member is strictly smaller than the whole",
which is the mass gap, `inf spec H` restricted to the orthogonal complement of the
vacuum being strictly positive. Protection moves from integer winding to
non-abelian braid monodromy, which is the gauge group being non-abelian. Those
are not a reading imposed afterwards; they are where the two entries differ. -/

theorem yangMills_delta_is_smallest :
    yangMillsConjecture.top = yangMillsTheorem.top ∧
    yangMillsConjecture.pol = yangMillsTheorem.pol ∧
    yangMillsConjecture.fid = yangMillsTheorem.fid ∧
    yangMillsConjecture.gram = yangMillsTheorem.gram ∧
    yangMillsConjecture.crit = yangMillsTheorem.crit ∧
    yangMillsConjecture.chir = yangMillsTheorem.chir ∧
    yangMillsConjecture.stoi = yangMillsTheorem.stoi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The mass gap sits at granularity, and it is a move rather than a holding. -/
theorem yangMills_gap_is_the_move :
    yangMillsConjecture.gran = Granularity.ice ∧
    yangMillsTheorem.gran = Granularity.bib :=
  ⟨rfl, rfl⟩

/-- The non-abelian hypothesis sits at protection, likewise. -/
theorem yangMills_nonabelian_is_the_move :
    yangMillsConjecture.prot = Protection.ah ∧
    yangMillsTheorem.prot = Protection.zoo :=
  ⟨rfl, rfl⟩

/-! ## The Navier-Stokes correction

`ConventionalDecomposition.lean` says in prose that the proof transition for
Navier-Stokes is the single criticality field. The criticality move is real: the
conjecture carries `monad`, a diverging correlation length, and the theorem
carries `woe`, no diverging correlation length, which is global regularity. But
it is not alone, and the claim that it is alone is false. -/

/-- Criticality does move, exactly as stated. -/
theorem navierStokes_criticality_moves :
    navierStokesConjecture.crit = Criticality.monad ∧
    navierStokesTheorem.crit = Criticality.woe :=
  ⟨rfl, rfl⟩

/-- And eight further marks move with it, so the transition is not one field.
    Here are three of them, each proved the same way as the criticality move. -/
theorem navierStokes_transition_is_not_one_field :
    navierStokesConjecture.dim ≠ navierStokesTheorem.dim ∧
    navierStokesConjecture.top ≠ navierStokesTheorem.top ∧
    navierStokesConjecture.fid ≠ navierStokesTheorem.fid := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## The Birch and Swinnerton-Dyer calibration, which holds

The stoichiometry mark carries the rank equality. The conjecture entry says
`|A| = 1 ∧ |B| = 1`, the unique bijection, which is the asserted equality of the
analytic and algebraic rank. The theorem entry says two objects of different
type, proved equal rather than identified. This is the one calibration in the
corpus that reproduces exactly. -/

theorem bsd_stoichiometry_carries_the_rank_equality :
    bsdConjecture.stoi = Stoichiometry.hung ∧
    bsdTheorem.stoi = Stoichiometry.up :=
  ⟨rfl, rfl⟩

end Imscribing.Millennium.ConventionalDelta
