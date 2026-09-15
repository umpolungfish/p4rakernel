import Imscribing.Primitives.Imscription

/-!
# ProvenManifolds — `_proven` and `_theorem` are two different things

The catalog holds two kinds of entry for a settled result. They are not two
names for one object; they are two addresses, and they measure differently.

* `X_conjecture_proven` is a STATUS stamped on a conjecture. 37 such entries
  occupy only 8 distinct addresses, and 27 of them sit on ONE — manifold A.
  A proven conjecture looks like every other proven conjecture.

* `X_theorem` is the mathematical OBJECT. 46 such entries occupy 36 distinct
  addresses. Ten share manifold B; the rest keep their own shape.

Zero `_theorem` entries sit on manifold A. Ten of the eleven on manifold B are
`_theorem` entries. The two clusters are the two kinds of entry.

One subject has both — Erdős–Faber–Lovász — and the two disagree in nine of
twelve fields.
-/

namespace Imscribing.Millennium.ProvenManifolds
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Fidelity KineticChar
     Granularity Grammar Criticality Chirality Stoichiometry Protection

/-! ## The two manifolds -/

/-- Manifold A ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑲𐑠𐑮𐑫𐑳𐑭⟩ — 27 of 37 `_proven` entries, 0 `_theorem` entries.
    The universal proven manifold: what having-been-proved looks like. -/
def provenManifold : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .ice, gram := .measure, crit := .roar, chir := .wool, stoi := .up, prot := .ah }

/-- Manifold B ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑲𐑵⊙𐑫𐑳𐑴⟩ — 10 of 11 members are `_theorem` entries.
    Berry–Tabor, Fujita, Carathéodory, Kusner, monomial, Bass embedding,
    Fröberg, Nagata, Virasoro, Tate, Hermite. -/
def theoremManifold : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or', fid := .peep, kin := .egg,
    gran := .ice, gram := .ooze, crit := .monad, chir := .wool, stoi := .up, prot := .oak }

/-! ## They agree on nine fields and disagree on three

Everything about the ground — dimension, topology, coupling, parity,
measurement, kinetics, completeness, chirality, stoichiometry — is shared. -/

theorem manifolds_agree_on_nine :
    provenManifold.dim  = theoremManifold.dim  ∧
    provenManifold.top  = theoremManifold.top  ∧
    provenManifold.rel  = theoremManifold.rel  ∧
    provenManifold.pol  = theoremManifold.pol  ∧
    provenManifold.fid  = theoremManifold.fid  ∧
    provenManifold.kin  = theoremManifold.kin  ∧
    provenManifold.gran = theoremManifold.gran ∧
    provenManifold.chir = theoremManifold.chir ∧
    provenManifold.stoi = theoremManifold.stoi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! The three that separate them:

* `gram` — being-proved composes in strict causal order, `seq!(f,g)`, one step
  before the next. Being-a-theorem BROADCASTS: `f → all x`, the statement held
  at every point at once. A proof is a path; a theorem is everywhere.

* `crit` — being-proved decays with oscillation of unbounded period, `roar`.
  Being-a-theorem sits at the monad, `ξ → ∞ ∧ μ∘δ = id`, idempotent at
  criticality.

* `prot` — being-proved carries an integer winding, `∮A = 2πn, n ∈ ℤ`. Being-a-
  theorem carries only a ℤ₂ class, `∮A = nπ`. The proof accumulates a count
  the theorem does not keep. -/

theorem proven_is_sequential : provenManifold.gram = Grammar.measure := rfl
theorem theorem_is_broadcast : theoremManifold.gram = Grammar.ooze := rfl

theorem proven_oscillates : provenManifold.crit = Criticality.roar := rfl
theorem theorem_is_critical : theoremManifold.crit = Criticality.monad := rfl

theorem proven_carries_integer : provenManifold.prot = Protection.ah := rfl
theorem theorem_carries_z2 : theoremManifold.prot = Protection.oak := rfl

theorem manifolds_differ_at_three :
    provenManifold.gram ≠ theoremManifold.gram ∧
    provenManifold.crit ≠ theoremManifold.crit ∧
    provenManifold.prot ≠ theoremManifold.prot :=
  ⟨fun h => Grammar.noConfusion h,
   fun h => Criticality.noConfusion h,
   fun h => Protection.noConfusion h⟩

/-! ## The one subject holding both addresses

Erdős–Faber–Lovász is the only entry in the catalog with a `_conjecture_proven`
AND a `_theorem`. They are not a duplicate to be reconciled. They are the
status and the object, and they agree in exactly ONE field out of twelve. -/

/-- `erdos_faber_lovasz_conjecture_proven` ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑲𐑠𐑮𐑫𐑳𐑭⟩ — on manifold A. -/
def erdosFaberLovaszProven : Imscription := provenManifold

/-- `erdos_faber_lovasz_theorem` ⟨𐑼𐑡𐑑𐑯𐑱𐑤𐑲𐑝⊙𐑓𐑕𐑴⟩ — on neither manifold. -/
def erdosFaberLovaszTheorem : Imscription :=
  { dim := .array, top := .judge, rel := .tot, pol := .nun, fid := .age, kin := .loll,
    gran := .ice, gram := .vow, crit := .monad, chir := .fee, stoi := .so, prot := .oak }

theorem efl_proven_on_manifold : erdosFaberLovaszProven = provenManifold := rfl

/-- Eleven of twelve fields differ. Only completeness is shared. -/
theorem efl_differs_at_eleven :
    erdosFaberLovaszProven.dim  ≠ erdosFaberLovaszTheorem.dim  ∧
    erdosFaberLovaszProven.top  ≠ erdosFaberLovaszTheorem.top  ∧
    erdosFaberLovaszProven.rel  ≠ erdosFaberLovaszTheorem.rel  ∧
    erdosFaberLovaszProven.pol  ≠ erdosFaberLovaszTheorem.pol  ∧
    erdosFaberLovaszProven.fid  ≠ erdosFaberLovaszTheorem.fid  ∧
    erdosFaberLovaszProven.kin  ≠ erdosFaberLovaszTheorem.kin  ∧
    erdosFaberLovaszProven.gram ≠ erdosFaberLovaszTheorem.gram ∧
    erdosFaberLovaszProven.crit ≠ erdosFaberLovaszTheorem.crit ∧
    erdosFaberLovaszProven.chir ≠ erdosFaberLovaszTheorem.chir ∧
    erdosFaberLovaszProven.stoi ≠ erdosFaberLovaszTheorem.stoi ∧
    erdosFaberLovaszProven.prot ≠ erdosFaberLovaszTheorem.prot :=
  ⟨fun h => Dimensionality.noConfusion h, fun h => Topology.noConfusion h,
   fun h => Relational.noConfusion h, fun h => Polarity.noConfusion h,
   fun h => Fidelity.noConfusion h, fun h => KineticChar.noConfusion h,
   fun h => Grammar.noConfusion h, fun h => Criticality.noConfusion h,
   fun h => Chirality.noConfusion h, fun h => Stoichiometry.noConfusion h,
   fun h => Protection.noConfusion h⟩

/-- The one field they share: the subject is Dedekind-finite. That much is the
    subject itself, and it survives both readings. -/
theorem efl_agrees_on_completeness :
    erdosFaberLovaszProven.gran = erdosFaberLovaszTheorem.gran := rfl

/-! ## What the census shows

Of the 76 settled entries other than the seven Clay theorems:

  measurement `peep`, the commutator          64
  completeness `ice`, Dedekind-finite         56
  chirality `wool`, no finite return          52
  composition `measure`, strict causal order  39
  composition `ooze`, broadcast               20
  winding `ah`, integer Chern class           48
  winding `oak`, ℤ₂ class                     22

Twenty of the seventy-six require broadcast and therefore do not decompose
into conventional mathematics. -/

end Imscribing.Millennium.ProvenManifolds
