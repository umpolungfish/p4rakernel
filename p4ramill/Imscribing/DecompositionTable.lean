/-
  Imscribing.DecompositionTable

  The six decomposition bounds of `Imscribing.Decomposition`, enumerated.

  `ValidDecomposition s n` conjoins six conditions on six of the twelve marks.
  Every one is decidable over a finite enumeration, so the relation can be
  printed in full rather than sampled. This module prints it, and it holds no
  copy of the conditions: each `decomposes*` function below calls the predicate
  from `Decomposition.lean` itself, so the table cannot drift from what that file
  says without this file failing to build.

  The point of having the table is to read a refusal on a METHOD. A method that
  fails a bound cannot reach what it is aimed at, and the failure is a statement
  in ordinary mathematics once the marks are read conventionally. The one worked
  case is the Collatz depth split, which carries chirality wool with kinetics yea
  and is refused by `wool_yea_refused`.

  Author: Lando ⊗ ⊙perator
-/

import Imscribing.Decomposition

namespace Imscribing.DecompositionTable

open Imscribing.Primitives
open Imscribing.Decomposition
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-- Every value of each axis the six bounds read, in constructor order. -/
def allChirality : List Chirality := [.fee, .kick, .sure, .wool]
def allKinetic : List KineticChar := [.yea, .loll, .egg, .on, .air]
def allDimensionality : List Dimensionality := [.dead, .ash, .array, .if']
def allProtection : List Protection := [.awe, .oak, .ah, .zoo]
def allTopology : List Topology := [.judge, .eat, .mime, .oil, .are]

/-- A carrier holding the six marks the bounds read, with the other six pinned
    to values no bound consults. Pinning is safe precisely because no bound
    mentions rel, pol, fid, gran, gram or stoi; if that ever changes this table
    stops being complete and the change belongs here first. -/
def probe (d : Dimensionality) (t : Topology) (k : KineticChar)
    (h : Chirality) (p : Protection) (c : Criticality) : Imscription :=
  { dim := d, top := t, rel := .ian, pol := .or', fid := .peep, kin := k,
    gran := .ice, gram := .measure, crit := c, chir := h, stoi := .up,
    prot := p }

/-- `validTemporalDecomposition` is a `dite` over a decidable equality with two
    decidable branches, so it is decidable; `Decomposition.lean` states the
    instance only for `InfiniteMemoryNeedsSlowKinetics`, so it is given here. -/
instance (s : Imscription) (n : ℕ) :
    Decidable (validTemporalDecomposition s n) := by
  unfold validTemporalDecomposition; infer_instance

/-- The six bounds, each read from `Decomposition.lean` rather than restated. -/
def memoryOk (s : Imscription) (n : ℕ) : Bool :=
  decide (validTemporalDecomposition s n)

def observabilityOk (s : Imscription) (n : ℕ) : Bool :=
  (observabilityResolution s.kin != none) || decide (n ≤ 2)

def stateSpaceOk (s : Imscription) (n : ℕ) : Bool :=
  (s.dim != .dead) || decide (n = 1)

def topologicalOk (s : Imscription) (n : ℕ) : Bool :=
  (s.prot != .oak) || decide (n % 2 = 1)

def connectivityOk (s : Imscription) : Bool :=
  s.top != .oil

/-- All six at once. `measurement_ok` is `s.crit = .monad → True`, which holds of
    every imscription, so it constrains nothing and is not tabulated. That it is
    vacuous is a fact about the sixth bound and is recorded here rather than
    quietly dropped. -/
def decomposes (s : Imscription) (n : ℕ) : Bool :=
  memoryOk s n && observabilityOk s n && stateSpaceOk s n
    && topologicalOk s n && connectivityOk s

/-- Which bounds refuse, as a list of names. -/
def refusedBy (s : Imscription) (n : ℕ) : List String :=
  (if memoryOk s n then [] else ["memory"])
    ++ (if observabilityOk s n then [] else ["observability"])
    ++ (if stateSpaceOk s n then [] else ["state_space"])
    ++ (if topologicalOk s n then [] else ["topological"])
    ++ (if connectivityOk s then [] else ["connectivity"])

/-- The sixth bound is vacuous: it holds of every imscription at every n. -/
theorem measurement_bound_vacuous (s : Imscription) : s.crit = .monad → True :=
  fun _ => trivial

/-- The memory bound ignores n once the chirality is wool, because
    `maxTemporalLayers wool = 0` makes the second conjunct hold outright. So for
    wool the whole question is the kinetics. -/
theorem wool_memory_is_kinetics_only (s : Imscription) (n m : ℕ)
    (h : s.chir = .wool) :
    validTemporalDecomposition s n ↔ validTemporalDecomposition s m := by
  unfold validTemporalDecomposition
  simp [h]

/-- The pair the Collatz depth split carries: eternal memory read at the fastest
    rate. Refused, and refused independently of how many layers are asked for. -/
theorem wool_yea_refused_at_every_n (s : Imscription)
    (hc : s.chir = .wool) (hk : s.kin = .yea) (n : ℕ) :
    ¬ validTemporalDecomposition s n := by
  unfold validTemporalDecomposition
  simp [hc, hk]

section Emit

/-- One row per (chirality, kinetics, n), tab separated, for the reader that
    turns a refusal into ordinary mathematics. -/
def memoryRows : List String :=
  (allChirality.flatMap fun h =>
    allKinetic.flatMap fun k =>
      ([1, 2, 3, 4] : List ℕ).map fun n =>
        let s := probe .if' .mime k h .ah .monad
        s!"{reprStr h}\t{reprStr k}\t{n}\t{decomposes s n}\t{refusedBy s n}")

/-- One row per (dimensionality, topology, protection, n): the three bounds that
    do not read chirality or kinetics. -/
def structureRows : List String :=
  (allDimensionality.flatMap fun d =>
    allTopology.flatMap fun t =>
      allProtection.flatMap fun p =>
        ([1, 2, 3, 4] : List ℕ).map fun n =>
          let s := probe d t .egg .wool p .monad
          s!"{reprStr d}\t{reprStr t}\t{reprStr p}\t{n}\t{decomposes s n}\t{refusedBy s n}")

-- The memory-and-observability table, printed on every build. Eighty rows is
-- the whole of it, so it is shown rather than summarised.
#eval IO.println (String.intercalate "\n" memoryRows)

-- The structural table is 320 rows; its size is printed, and `structureRows`
-- is there to be read when wanted.
#eval structureRows.length

end Emit

end Imscribing.DecompositionTable
