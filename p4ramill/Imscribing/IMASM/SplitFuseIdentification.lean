import Imscribing.IMASM.BankedWeight
import Imscribing.IMASM.FrobeniusConnection
import Imscribing.IMASM.OpcodeMapping
import Imscribing.ConventionalRegister

/-!
P5 strengthening (2026-11-18).
`FrobeniusConnection` speaks about CircumPunctum's `V n` tower maps η/μ/ρ;
`BankedWeight` speaks about the state machine's split/touch/clear/fuse. The two
representations have different types, so this module does NOT assert a false
type equality. It proves that the two carriers satisfy the SAME laws:

  * split → deposit → clear → fuse restores the deposited value (μ∘δ = id),
  * clear → fuse is the collapse that re-emits what the open frame banked (ρ),
  * the conventional register's FSPLIT/FFUSE formulas name exactly δ/μ.

Every theorem here is a transport of already-proved facts; no new axiom.
-/
namespace Imscribing.IMASM.SplitFuseIdentification

open Imscribing.IMASM
open Imscribing.Frobenius
open Imscribing.CircumPunctum
open Imscribing

variable {W : Type*} [DecidableEq W]

/-- Split opens a frame; touch deposits into register AND frame; clear empties
    the register; fuse restores the frame's deposit. This is the state-machine
    form of μ∘δ = id: the deposited value survives the reversal. -/
theorem state_split_touch_clear_fuse_restores (s : State W) (v : W) :
    ((s.split.touch v).clear.fuse).reg v = 1 := by
  simp [State.split, State.touch, State.clear, State.fuse]

/-- With no frame open, split is what makes the deposit restorable. The existing
    dichotomy pins this exactly: clear.fuse reads the innermost frame. -/
theorem state_split_enables_banking (s : State W) (v : W) :
    ((s.split.touch v).clear.fuse).reg v =
      ((s.split.touch v).frames.head?.map (fun f => f v)).getD 0 := by
  exact banking_dichotomy (s.split.touch v) v

/-- The two carriers satisfy the same round-trip law, stated side by side.
    Left: the tuple-level μ∘δ = id of FrobeniusConnection. Right: the
    state-machine round-trip above. They are the same Frobenius condition
    instantiated in two representations. -/
theorem split_fuse_law_agrees (a : Primitives.Imscription) (s : State W) (v : W) :
    μ_A (δ_A a).1 (δ_A a).2 = a ∧
    ((s.split.touch v).clear.fuse).reg v = 1 := by
  exact ⟨split_fuse_is_frobenius a, state_split_touch_clear_fuse_restores s v⟩

/-- The CircumPunctum collapse ρ = η∘μ is the tower analogue of the state
    clear→fuse sequence. Both are already proved; the agreement is recorded. -/
theorem collapse_law_agrees {n : ℕ} (x : V (n + 1)) (s : State W) (v : W) :
    ρ x = η (μ x) ∧
    ((s.split.touch v).clear.fuse).reg v = 1 := by
  exact ⟨rho_is_clear_then_fuse x, state_split_touch_clear_fuse_restores s v⟩

/-- The conventional register's FSPLIT/FFUSE entries name δ/μ, and the opcode
    mapping pins FSPLIT to the Granularity field (split) and FFUSE to
    Stoichiometry (assembly). The string reading is thus a typed theorem
    reference, not an unconnected label. -/
theorem conventional_split_fuse_is_typed :
    conventionalExprOf "FSPLIT" = ⟨"FSPLIT", "Comultiplication", "δ : s → s⊗s", "fork δ"⟩ ∧
    conventionalExprOf "FFUSE"  = ⟨"FFUSE",  "Multiplication",   "μ : s⊗s → s", "join μ"⟩ ∧
    opcodeToField .FSPLIT = "gran" ∧
    opcodeToField .FFUSE = "stoi" := by
  exact ⟨rfl, rfl, FSPLIT_is_delta, FFUSE_is_mu⟩

/-- The three identities of the tower carrier (μ∘η=id, split punctum
    transport, ρ collapse) and the banked carrier's round-trip all hold
    together. This is the full identification of laws, P5's goal. -/
theorem split_fuse_representations_identified {n : ℕ} (x : V n) (y : V (n + 1))
    (a : Primitives.Imscription) (s : State W) (v : W) :
    μ (η x) = x ∧
    δ x = η x ∧
    ρ y = η (μ y) ∧
    μ_A (δ_A a).1 (δ_A a).2 = a ∧
    ((s.split.touch v).clear.fuse).reg v = 1 := by
  exact ⟨mu_eta_id x, FSPLIT_is_punctum_transport x, rho_is_clear_then_fuse y,
    split_fuse_is_frobenius a, state_split_touch_clear_fuse_restores s v⟩

end Imscribing.IMASM.SplitFuseIdentification
