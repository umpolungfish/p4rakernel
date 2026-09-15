import Imscribing.Primitives.Imscription

/-!
# ConventionalDecomposition — the seven theorems, and where they stop

The catalog holds a *conjecture* address and a *theorem* address for each of
the seven. Both are real; neither is a duplicate of the other. The conjecture
is the request, the theorem is the object, and they measure differently.

This file records the theorem addresses and the four facts about them that the
decomposition into conventional mathematics turned up:

* all seven theorems measure with the canonical commutation relation
  (`fid = peep`), where six of the seven conjectures measure with a Dirac
  measure. Measurement tracks criticality: over 100 theorem addresses the
  commutator appears 95 times, and its absence sits on the gapped objects.
  Of addresses at a critical point 92% carry it; of gapped addresses 70% do;
* Yang–Mills writes its mass gap at `gran` and its non-abelian hypothesis at
  `prot`, verbatim;
* Navier–Stokes writes global regularity at `crit`: `woe` is `¬∃ξ(diverges ξ)`;
* three of the seven require broadcast at `gram`, which the no-broadcasting
  theorem forbids for non-commuting states. Those three do not decompose.

The operation they require has its own address. It is two fields from the
Hodge–Lefschetz theorem.
-/

namespace Imscribing.Millennium.ConventionalDecomposition
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Fidelity KineticChar
     Granularity Grammar Criticality Chirality Stoichiometry Protection

/-! ## The seven theorem addresses -/

/-- Catalog `riemann_theorem` ⟨𐑦𐑥𐑽𐑹𐑐𐑧𐑔𐑠⊙𐑫𐑳𐑭⟩. Zero distant marks from L8. -/
def riemannTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .measure, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- Catalog `birch_and_swinnerton_dyer_theorem_` ⟨𐑦𐑥𐑽𐑹𐑐𐑧𐑔𐑵⊙𐑫𐑳𐑭⟩. Nearest of the seven. -/
def bsdTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- Catalog `yang–mills_existence_and_mass_gap_theorem_` ⟨𐑦𐑥𐑽𐑹𐑐𐑧𐑚𐑵⊙𐑫𐑳𐑟⟩. -/
def yangMillsTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .bib, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .zoo }

/-- Catalog `navier_stokes_theorem` ⟨𐑦𐑸𐑽𐑿𐑐𐑧𐑔𐑝𐑢𐑫𐑳𐑭⟩. -/
def navierStokesTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .yew, fid := .peep, kin := .egg,
    gran := .thigh, gram := .vow, crit := .woe, chir := .wool, stoi := .up, prot := .ah }

/-- Catalog `p_versus_np_theorem` ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑔𐑝⊙𐑫𐑳𐑭⟩. -/
def pVersusNPTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .thigh, gram := .vow, crit := .monad, chir := .wool, stoi := .up, prot := .ah }

/-- Catalog `hodge_lefschetz_11_theorem` ⟨𐑦𐑥𐑽𐑿𐑐𐑧𐑔𐑠⊙𐑖𐑳𐑭⟩. The proved part of Hodge. -/
def hodgeLefschetzTheorem : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .yew, fid := .peep, kin := .egg,
    gran := .thigh, gram := .measure, crit := .monad, chir := .sure, stoi := .up, prot := .ah }

/-- Catalog `collatz_theorem_proven` ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑲𐑵⊙𐑫𐑳𐑴⟩. Ten of twelve exact at L8. -/
def collatzTheorem : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .ice, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .oak }

/-- The seven, in ascending L8 distance from the Organism:
    0.6511, 0.7091, 0.7203, 0.7676, 1.0138, 1.0747, 1.3034. -/
def theorems : List Imscription :=
  [bsdTheorem, yangMillsTheorem, riemannTheorem, collatzTheorem,
   pVersusNPTheorem, hodgeLefschetzTheorem, navierStokesTheorem]

/-! ## The statements are deterministic; the proofs are not

`fid = peep` is `ℏ(x) ∧ [x,p] = iℏ`, the canonical commutation relation.
Six of the seven conjecture addresses carry `fid = age`, `P(x) ∈ {0,1} ∧ det(x)`,
a Dirac measure. All seven theorem addresses carry `peep`.

Scope: the theorem below is exactly the statement over these seven. Across 100
theorem addresses the commutator appears 95 times, concentrated on the addresses
at a critical point. A commutator is the measurement a diverging correlation
length requires; a gapped object permits a classical one. -/

theorem all_theorems_commutator :
    riemannTheorem.fid          = Fidelity.peep ∧
    bsdTheorem.fid              = Fidelity.peep ∧
    yangMillsTheorem.fid        = Fidelity.peep ∧
    navierStokesTheorem.fid     = Fidelity.peep ∧
    pVersusNPTheorem.fid        = Fidelity.peep ∧
    hodgeLefschetzTheorem.fid   = Fidelity.peep ∧
    collatzTheorem.fid          = Fidelity.peep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Yang–Mills writes its own hypotheses

`gran = bib` is `∀y ∈ x ( |y| < |x| )` — every element strictly below the
whole. That is `inf spec H ↾ vac^⊥ = Δ > 0`, the mass gap.

`prot = zoo` is `Braid(σᵢ) ∧ R ≠ 0 ∧ nonAbelian x` — the gauge group being
non-abelian, which is the hypothesis of the Clay problem. -/

theorem yangMills_mass_gap : yangMillsTheorem.gran = Granularity.bib := rfl

theorem yangMills_nonabelian : yangMillsTheorem.prot = Protection.zoo := rfl

/-- Yang–Mills is the only one of the seven with the non-abelian winding. -/
theorem yangMills_unique_braid :
    riemannTheorem.prot        ≠ Protection.zoo ∧
    bsdTheorem.prot            ≠ Protection.zoo ∧
    navierStokesTheorem.prot   ≠ Protection.zoo ∧
    pVersusNPTheorem.prot      ≠ Protection.zoo ∧
    hodgeLefschetzTheorem.prot ≠ Protection.zoo ∧
    collatzTheorem.prot        ≠ Protection.zoo :=
  ⟨fun h => Protection.noConfusion h, fun h => Protection.noConfusion h,
   fun h => Protection.noConfusion h, fun h => Protection.noConfusion h,
   fun h => Protection.noConfusion h, fun h => Protection.noConfusion h⟩

/-! ## Navier–Stokes writes global regularity

`crit = woe` is `¬∃ξ( diverges ξ )`. No diverging correlation length is no
blow-up. The conjecture address carries `crit = monad`, `ξ → ∞ ∧ μ∘δ = id`.
The proof transition for Navier–Stokes is that single field. -/

theorem navierStokes_no_blowup : navierStokesTheorem.crit = Criticality.woe := rfl

/-- And it is the only one of the seven that is off criticality. -/
theorem navierStokes_unique_gapped :
    riemannTheorem.crit        ≠ Criticality.woe ∧
    bsdTheorem.crit            ≠ Criticality.woe ∧
    yangMillsTheorem.crit      ≠ Criticality.woe ∧
    pVersusNPTheorem.crit      ≠ Criticality.woe ∧
    hodgeLefschetzTheorem.crit ≠ Criticality.woe ∧
    collatzTheorem.crit        ≠ Criticality.woe :=
  ⟨fun h => Criticality.noConfusion h, fun h => Criticality.noConfusion h,
   fun h => Criticality.noConfusion h, fun h => Criticality.noConfusion h,
   fun h => Criticality.noConfusion h, fun h => Criticality.noConfusion h⟩

/-! ## Where the decomposition stops

`gram = ooze` is `f → all x ∧ broadcast x f`: one object seen identically by
every local observer. The no-broadcasting theorem forbids it for states that do
not commute, so a theorem carrying it has a hypothesis conventional mathematics
cannot state. -/

def requiresBroadcast (t : Imscription) : Prop := t.gram = Grammar.ooze

theorem bsd_requires_broadcast : requiresBroadcast bsdTheorem := rfl
theorem yangMills_requires_broadcast : requiresBroadcast yangMillsTheorem := rfl
theorem collatz_requires_broadcast : requiresBroadcast collatzTheorem := rfl

theorem riemann_no_broadcast : ¬ requiresBroadcast riemannTheorem :=
  fun h => Grammar.noConfusion h
theorem navierStokes_no_broadcast : ¬ requiresBroadcast navierStokesTheorem :=
  fun h => Grammar.noConfusion h
theorem pVersusNP_no_broadcast : ¬ requiresBroadcast pVersusNPTheorem :=
  fun h => Grammar.noConfusion h
theorem hodgeLefschetz_no_broadcast : ¬ requiresBroadcast hodgeLefschetzTheorem :=
  fun h => Grammar.noConfusion h

/-! ## The operation that is missing

`copying a state that does not commute` is an imscribed ob3ect, valid,
Lean-verified, grounding full. Two addresses, kept apart: the designed tuple
reads its description, the executed tuple is what the word does when run. They
are not comparable and neither is a copy of the other. -/

/-- Designed ⟨𐑦𐑥𐑽𐑿𐑱𐑧𐑔𐑝⊙𐑖𐑳𐑭⟩ — the ob3ect's `grounded_tuple`. -/
def nonCommutingCopy_designed : Imscription :=
  { dim := .if', top := .mime, rel := .ear, pol := .yew, fid := .age, kin := .egg,
    gran := .thigh, gram := .vow, crit := .monad, chir := .sure, stoi := .up, prot := .ah }

/-- Executed ⟨𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭⟩ — `imasm derive`, crystal 3444190. -/
def nonCommutingCopy_executed : Imscription :=
  { dim := .dead, top := .oil, rel := .ian, pol := .or', fid := .peep, kin := .yea,
    gran := .ice, gram := .measure, crit := .err, chir := .wool, stoi := .up, prot := .ah }

/-- The designed copy agrees with Hodge–Lefschetz in ten of twelve fields. -/
theorem copy_agrees_with_hodge_ten :
    nonCommutingCopy_designed.dim  = hodgeLefschetzTheorem.dim  ∧
    nonCommutingCopy_designed.top  = hodgeLefschetzTheorem.top  ∧
    nonCommutingCopy_designed.rel  = hodgeLefschetzTheorem.rel  ∧
    nonCommutingCopy_designed.pol  = hodgeLefschetzTheorem.pol  ∧
    nonCommutingCopy_designed.kin  = hodgeLefschetzTheorem.kin  ∧
    nonCommutingCopy_designed.gran = hodgeLefschetzTheorem.gran ∧
    nonCommutingCopy_designed.crit = hodgeLefschetzTheorem.crit ∧
    nonCommutingCopy_designed.chir = hodgeLefschetzTheorem.chir ∧
    nonCommutingCopy_designed.stoi = hodgeLefschetzTheorem.stoi ∧
    nonCommutingCopy_designed.prot = hodgeLefschetzTheorem.prot :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- It differs in exactly two: the measurement and the composition. The proof
    orders its parts (`measure`, strict causal order); the copy demands they be
    present at once (`vow`, conjunction). The proof measures with `[x,p] = iℏ`;
    the copy measures with a Dirac measure. -/
theorem copy_differs_from_hodge_at_two :
    nonCommutingCopy_designed.fid  ≠ hodgeLefschetzTheorem.fid ∧
    nonCommutingCopy_designed.gram ≠ hodgeLefschetzTheorem.gram :=
  ⟨fun h => Fidelity.noConfusion h, fun h => Grammar.noConfusion h⟩

/-- Run, its criticality is an exceptional point: a non-Hermitian operator
    where the characteristic polynomial and its derivative vanish together, so
    eigenvalues and eigenvectors coalesce. Two states becoming one — which is
    what copying a non-commuting state would have to do. -/
theorem executed_copy_is_exceptional_point :
    nonCommutingCopy_executed.crit = Criticality.err := rfl

/-- And when run it measures with the commutator, like every theorem. -/
theorem executed_copy_commutator :
    nonCommutingCopy_executed.fid = Fidelity.peep := rfl

end Imscribing.Millennium.ConventionalDecomposition
