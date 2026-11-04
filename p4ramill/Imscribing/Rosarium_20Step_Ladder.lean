/-
Rosarium Philosophorum — 20-Step Ladder
Formal companion: Dialetheic Bootstrap protocol scaffold
Generated from proof_scaffold canonical="I_Dialetheic_Bootstrap"
Mapped to Rosarium woodcut sequence via opcode_map
-/

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality
open CategoryTheory

-- ── Rosarium base imscription (O_inf: monad + or') ───────────────────────

def rosarium_s : Imscription :=
  { dim := array, top := are, rel := ian, pol := or', fid := peep, kin := egg,
    gran := ice, gram := measure, crit := monad, chir := wool, stoi := up, prot := zoo }

-- ── Main scaffold: IGProtocol with correct constructor syntax ─────────────
-- 8 arrows chained by .seq, each contributing depth 1 → total depth 8

noncomputable def rosarium_20step_protocol :
    IGProtocol rosarium_s rosarium_s :=
  .withGram Grammar.measure <|
  .withMem Chirality.wool <|
  (.seq
    (.arrow rosarium_s rosarium_s rosarium_s)   -- [0] IMSCRIB / WC20: Glorification
    (.seq
      (.arrow rosarium_s rosarium_s rosarium_s)   -- [1] EVALT / WC11–12: Rebirth–Pelican
      (.seq
        (.arrow rosarium_s rosarium_s rosarium_s)   -- [2] AFWD / WC3: Naked Truth
        (.seq
          (.arrow rosarium_s rosarium_s rosarium_s)   -- [3] EVALF / WC14: Hermaphrodite
          (.seq
            (.arrow rosarium_s rosarium_s rosarium_s)   -- [4] FFUSE / WC10: Soul Returning
            (.seq
              (.arrow rosarium_s rosarium_s rosarium_s)   -- [5] ENGAGR / WC16: King from Fire
              (.seq
                (.arrow rosarium_s rosarium_s rosarium_s)   -- [6] IFIX / WC17: Serpent Sacrifice
                (.arrow rosarium_s rosarium_s rosarium_s)   -- [7] IMSCRIB / WC20: Glorification — closure
              )
            )
          )
        )
      )
    )
  )

-- ── Verification theorems ─────────────────────────────────────────────────

theorem rosarium_tier : TierFunctor.obj rosarium_s = .O_inf := by
  rw [TierFunctor_obj]
  -- rosarium_s: crit=monad, pol=or' → R1 gives O_inf
  decide

theorem rosarium_loop_closure :
    ∃ (loop : IGProtocol rosarium_s rosarium_s),
      loop = rosarium_20step_protocol ∧
      loop.depth ≥ 1 := by
  have h₁ : rosarium_20step_protocol.depth ≥ 1 := by
    have h₂ : rosarium_20step_protocol.depth = 8 := by
      -- 8 arrows chained sequentially → depth 8
      simp [rosarium_20step_protocol, IGProtocol.depth]
      <;> norm_num
      <;> decide
    omega
  refine' ⟨rosarium_20step_protocol, rfl, h₁⟩
  <;> decide

end Imscribing
