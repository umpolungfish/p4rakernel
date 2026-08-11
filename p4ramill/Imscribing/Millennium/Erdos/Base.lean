-- Imscribing/Millennium/Erdos/Base.lean
-- What every Erdős problem file shares.
--
-- The Belnap branch type lived in the header of the old single-file
-- ErdosProblems.lean. Splitting one problem per file left fifteen files needing
-- it, so it lives here once and they import it. One definition, one home.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription

namespace Millennium.ErdosProblems

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/--
FSPLIT:δ decomposes a problem into its Belnap structural branches:
structural (algebraic), statistical (probabilistic), obstructional
(counterexample/barrier).
-/
inductive FsplitBranch where
  | structural
  | statistical
  | obstructional
  deriving DecidableEq, Repr

end Millennium.ErdosProblems
