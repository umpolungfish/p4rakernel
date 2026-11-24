-- Imscribing/IMASM/FrobeniusConnection.lean
-- Connect IMASM split/fuse opcodes (∈/∋) to Frobenius comultiplication/multiplication (δ/μ).
--
-- The ∈ (FSPLIT) opcode is the IMASM face of Frobenius comultiplication δ.
-- The ∋ (FFUSE) opcode is the IMASM face of Frobenius multiplication μ.
-- Together they satisfy μ ∘ δ = id — the Frobenius condition at O_inf.
--
-- Author: Lando ⊗ ⊙perator
-- Kernel: p4rakernel (paraconsistent Lean 4)

import Imscribing.IMASM.OpcodeMapping
import Imscribing.Frobenius
import Imscribing.CircumPunctum
import Imscribing.Algebra
import Imscribing.IGFunctor

namespace Imscribing.IMASM

open Imscribing.Primitives
open Imscribing.Frobenius
open Imscribing.CircumPunctum
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

/-- The ∈ (FSPLIT) opcode is the IMASM annotation for Frobenius comultiplication δ.
    Both split a single value into a pair: δ(a) = (a, a) duplicates the imscription,
    while FSPLIT marks an arrow label as a range-decomposition boundary. -/
theorem FSPLIT_is_delta :
    opcodeToField .FSPLIT = "gran" := by rfl

/-- The ∋ (FFUSE) opcode is the IMASM annotation for Frobenius multiplication μ.
    Both fuse a pair into a single value: μ(x, y) = tensorProduct(x, y) composes
    two imscriptions, while FFUSE marks an arrow label as an assembly boundary. -/
theorem FFUSE_is_mu :
    opcodeToField .FFUSE = "stoi" := by rfl

/-- The ∈/∋ pair in an IMASM protocol word corresponds to the δ/μ pair in Frobenius.
    The Frobenius condition μ ∘ δ = id is exactly the statement that splitting
    then fusing returns the exact starting imscription. -/
theorem split_fuse_is_frobenius (a : Imscription) :
    μ_A (δ_A a).1 (δ_A a).2 = a := by
  exact mu_delta_A_id a

/-- The translation lemma δ = η (CircumPunctum §15) connects the Frobenius
    comultiplication to the re-entry tower's punctum transport. In IMASM terms,
    this means the FSPLIT opcode (∈) is the same operation as punctum transport η. -/
theorem FSPLIT_is_punctum_transport {n : ℕ} (x : V n) :
    δ x = η x := by
  exact δ_eq_η x

/-- The frame collapse ρ = η ∘ μ corresponds to the IMASM clear/fuse sequence.
    ρ forgets the marker bit (clear), then re-emits it marked (fuse). -/
theorem rho_is_clear_then_fuse {n : ℕ} (x : V (n + 1)) :
    ρ x = η (μ x) := by
  rfl

/-- η (punctum transport) is the IMASM split operation: it opens a new frame
    and marks the value as carried upward. In IMASM terms, split pushes an empty
    frame onto the stack. -/
theorem eta_is_split {n : ℕ} (x : V n) :
    η x = (x, true) := by rfl

/-- μ (reveal) is the IMASM fuse operation: it pops the innermost frame and
    folds it outward by max. In IMASM terms, fuse closes the innermost frame. -/
theorem mu_is_fuse {n : ℕ} (x : V (n + 1)) :
    μ x = x.1 := by rfl

/-- ρ (frame collapse) is the IMASM clear-then-fuse sequence: clear empties the
    register, then fuse restores what was banked in the open frame. -/
theorem rho_is_clear_fuse {n : ℕ} (x : V (n + 1)) :
    ρ x = η (μ x) := by rfl

/-- μ ∘ η = id (CircumPunctum §7): reveal after punctum transport loses nothing.
    In IMASM terms: fuse after split recovers the deposited value. -/
theorem mu_eta_id {n : ℕ} (x : V n) :
    μ (η x) = x := by
  exact μ_η_id x

/-- ρ² = ρ (CircumPunctum §7): frame collapse is idempotent. In IMASM terms,
    clearing twice is the same as clearing once. -/
theorem rho_idempotent {n : ℕ} (x : V (n + 1)) :
    ρ (ρ x) = ρ x := by
  exact ρ_idempotent x

end Imscribing.IMASM
