import Imscribing.IUTT
import Init.Paraconsistent

/-!
Finite tensor filtration: lane closure, native re-entry, projection readouts,
the phase-weighted trace compiler, and the symmetric sector ladder.
-/

namespace Imscribing.Paraconsistent.TensorFiltration

open Imscribing.IUTT

/-- The lane presentation and native membership presentation agree on all gates.
Truth-positive/constructivity-positive T maps to B; F to F; t to T; f to N. -/
def nativeCarrier : State ≃ Lean.Sixteen3 where
  toFun x := ⟨x.smallF, x.smallT, x.bigF, x.bigT⟩
  invFun x := (x.hasB, x.hasF, x.hasT, x.hasN)
  left_inv x := by rcases x with ⟨a, b, c, d⟩; rfl
  right_inv x := by cases x; rfl

theorem native_union : ∀ x y : State,
    nativeCarrier (x.union y) = Lean.Sixteen3.join_i (nativeCarrier x) (nativeCarrier y) :=
  by decide

theorem native_truth_meet : ∀ x y : State,
    nativeCarrier (x.meetT y) = Lean.Sixteen3.meet_t (nativeCarrier x) (nativeCarrier y) :=
  by decide

theorem native_constructivity_join : ∀ x y : State,
    nativeCarrier (x.joinC y) = Lean.Sixteen3.join_f (nativeCarrier x) (nativeCarrier y) :=
  by decide

enable_trilattice

/-- Native least information fixed point corresponding to the t,f lane seed. -/
reentry nativeAmbient (x : Lean.Sixteen3) : Lean.Sixteen3 :=
  Lean.Sixteen3.join_i x (Lean.Sixteen3.ofBelnap true true false false)

disable_trilattice

theorem native_ambient_agrees : nativeAmbient = nativeCarrier ambient := rfl

def eta (x : State) : State := x.union ambient

inductive Branch where
  | truth | information | falsity
  deriving DecidableEq, Repr

/-- Insert the information seed into the selected arm, then fuse all arms. -/
def branch (arm : Branch) : State → State :=
  match arm with
  | .truth => transport eta id id
  | .information => transport id eta id
  | .falsity => transport id id eta

theorem branch_agrees : ∀ arm x, branch arm x = eta x := by
  intro arm; cases arm <;> decide

inductive Word where
  | generator : Branch → Word
  | compose : Word → Word → Word
  deriving DecidableEq, Repr

def Word.evaluate : Word → State → State
  | .generator arm => branch arm
  | .compose a b => a.evaluate ∘ b.evaluate

def thetaWord : Word :=
  .compose (.generator .truth)
    (.compose (.generator .information) (.generator .falsity))

def theta : State → State := thetaWord.evaluate

theorem theta_eq_eta : ∀ x, theta x = eta x := by decide
theorem theta_idempotent : ∀ x, theta (theta x) = theta x := by decide
theorem theta_proper : theta empty ≠ empty := by decide
theorem theta_fixed_iff : ∀ x, theta x = x ↔ x.smallT = true ∧ x.smallF = true :=
  by decide
theorem theta_fixed_count : Fintype.card {x : State // theta x = x} = 4 := by decide
theorem theta_least : ∀ x y : State,
    Reg16_3.leqI x y → theta y = y → Reg16_3.leqI (theta x) y := by decide
theorem theta_extensive : ∀ x : State, Reg16_3.leqI x (theta x) := by decide
theorem theta_monotone : ∀ x y : State,
    Reg16_3.leqI x y → Reg16_3.leqI (theta x) (theta y) := by decide

/-- The lane representation of closure is exactly native information join. -/
theorem native_theta : ∀ x : State,
    nativeCarrier (theta x) = Lean.Sixteen3.join_i (nativeCarrier x) nativeAmbient :=
  by decide

/-- The abstract branch representation satisfies the normalized loop relations. -/
theorem branch_loop : ∀ a b x, branch a (branch b (branch a x)) = branch a x :=
  by intro a b; cases a <;> cases b <;> decide

abbrev ConstructiveFour := Bool × Bool
def constructiveReadout (x : State) : ConstructiveFour := (x.bigT, x.bigF)
def constructiveInclusion (x : ConstructiveFour) : State := (x.1, x.2, false, false)

theorem constructive_retraction (x : ConstructiveFour) :
    constructiveReadout (constructiveInclusion x) = x := rfl
theorem erasure_factors : ∀ x,
    eraseInformation x = constructiveInclusion (constructiveReadout x) := by decide
theorem constructive_cardinality : Fintype.card ConstructiveFour = 4 := by decide
theorem boolean_shadow_formula : ∀ x,
    booleanShadow x = if x.bigT && !x.bigF then Belnap.T else Belnap.F := by decide

/-- Closure and erasure commute after erasure has been applied to the output. -/
theorem erasure_theta : ∀ x, eraseInformation (theta x) = eraseInformation x := by decide
theorem projection_forgets_closure : ∀ x,
    eraseInformation (theta (eraseInformation x)) = eraseInformation x := by decide

/-- Matrix readout retaining all four lanes as its four entries. -/
def matrixReadout (x : State) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![if x.bigT then 1 else 0, if x.smallT then 1 else 0;
     if x.smallF then 1 else 0, if x.bigF then 1 else 0]

def dephase (M : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => if i = j then M i j else 0

theorem matrix_projection_commutes (x : State) :
    dephase (matrixReadout x) = matrixReadout (eraseInformation x) := by
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem dephase_idempotent (M : Matrix (Fin 2) (Fin 2) ℚ) :
    dephase (dephase M) = dephase M := by
  funext i j
  by_cases h : i = j <;> simp [dephase, h]

def held (x : State) : Bool := x.smallT && x.smallF
def phaseWeight (j : Fin 12) : Nat := (j.val + 1)^2
def phaseSum : Nat := ∑ j : Fin 12, phaseWeight j
theorem phase_sum : phaseSum = 650 := by decide

def weightedTrace (x : State) : Nat := if held x then phaseSum else 0
theorem theta_trace : ∀ x, weightedTrace (theta x) = 650 := by decide
theorem erased_trace : ∀ x, weightedTrace (eraseInformation x) = 0 := by decide

theorem trace_does_not_factor_through_erasure :
    ¬ ∃ f : State → Nat, ∀ x, weightedTrace x = f (eraseInformation x) := by
  rintro ⟨f, hf⟩
  have heq : weightedTrace (theta empty) = weightedTrace empty := by
    rw [hf (theta empty), hf empty, erasure_theta]
  have hzero : weightedTrace empty = 0 := by decide
  rw [theta_trace, hzero] at heq
  contradiction

/-- The phase-weighted trace is the ordinary trace of this diagonal operator. -/
def phaseOperator (x : State) : Matrix (Fin 12) (Fin 12) Nat :=
  Matrix.diagonal (fun j => if held x then phaseWeight j else 0)

theorem phase_operator_trace (x : State) : (phaseOperator x).trace = weightedTrace x := by
  by_cases h : held x = true <;> simp [phaseOperator, weightedTrace, phaseSum, h]

/-- The ordinary free-carrier linearization has one diagonal entry per fixed state. -/
def carrierOperator : Matrix State State Nat := fun y x => if theta x = y then 1 else 0
theorem carrier_operator_trace : carrierOperator.trace = 4 := by decide

inductive Op where
  | readFiltration : Fin 12 → Op
  | add
  | erase
  | divide : Nat → Op
  deriving DecidableEq, Repr

structure Machine where
  state : State
  pending : Nat := 0
  accumulator : Nat := 0
  deriving DecidableEq, Repr

def step (machine : Machine) : Op → Machine
  | .readFiltration j => { machine with pending := phaseWeight j }
  | .add => { machine with accumulator := machine.accumulator +
      (if held machine.state then machine.pending else 0) }
  | .erase => { machine with state := eraseInformation machine.state }
  | .divide n => { machine with accumulator := machine.accumulator / n }

def execute (code : List Op) (seed : State) : Machine :=
  code.foldl step { state := seed }

def traceProgram : List Op :=
  (List.finRange 12).flatMap (fun j => [.readFiltration j, .add])

def audit (code : List Op) : Bool := code.all fun op =>
  match op with
  | .readFiltration _ | .add => true
  | .erase | .divide _ => false

structure Program where
  seed : State
  code : List Op

def lower (word : Word) (input : State) : Program :=
  ⟨word.evaluate input, traceProgram⟩

theorem compiler_length : traceProgram.length = 24 := by decide
theorem compiler_audit : audit traceProgram = true := by decide
theorem execution_trace : ∀ x,
    (execute traceProgram x).accumulator = weightedTrace x := by decide
theorem compiled_theta_trace (x : State) :
    (execute (lower thetaWord x).code (lower thetaWord x).seed).accumulator = 650 := by
  change (execute traceProgram (theta x)).accumulator = 650
  rw [execution_trace, theta_trace]

/-- Audit soundness is stated for programs extracted by the canonical compiler. -/
theorem audited_extracted_trace (program : Program)
    (hextracted : ∃ x, program = lower thetaWord x) (_haudit : audit program.code = true) :
    (execute program.code program.seed).accumulator = 650 := by
  obtain ⟨x, rfl⟩ := hextracted
  exact compiled_theta_trace x

theorem audit_rejects_erasure : audit [.erase] = false := rfl
theorem audit_rejects_division (n : Nat) : audit [.divide n] = false := rfl

/-- A sector ladder on the m+1 uniform weight sectors. -/
noncomputable def raise (m : Nat) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  fun i j => if i.val = j.val + 1 then
    Real.sqrt (((j.val + 1) * (m - j.val) : Nat) : ℝ) else 0

noncomputable def lowerSector (m : Nat) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  (raise m).transpose

noncomputable def ladder (m : Nat) (d : ℝ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  fun i j => (if i = j then (i.val : ℝ) * d else 0) + raise m i j + raise m j i

theorem lower_is_transpose (m : Nat) : lowerSector m = (raise m).transpose := rfl

theorem ladder_symmetric (m : Nat) (d : ℝ) (i j : Fin (m+1)) :
    ladder m d i j = ladder m d j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [ladder, h, Ne.symm h, if_false]
    ring

theorem ladder_diagonal (m : Nat) (d : ℝ) (i : Fin (m+1)) :
    ladder m d i i = (i.val : ℝ) * d := by
  simp [ladder, raise]

theorem ladder_off_diagonal (m : Nat) (d : ℝ) (i j : Fin (m+1))
    (h : i.val = j.val + 1) :
    ladder m d i j = Real.sqrt (((j.val + 1) * (m - j.val) : Nat) : ℝ) := by
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hji : j.val ≠ i.val + 1 := by omega
  unfold ladder raise
  rw [if_neg hij, if_pos h, if_neg hji]
  simp

theorem ladder_tridiagonal (m : Nat) (d : ℝ) (i j : Fin (m+1))
    (hdiag : i ≠ j) (hup : i.val ≠ j.val + 1) (hdown : j.val ≠ i.val + 1) :
    ladder m d i j = 0 := by
  simp [ladder, raise, hdiag, hup, hdown]

theorem raised_weight_square (m : Nat) (j : Fin (m+1)) :
    (Real.sqrt (((j.val + 1) * (m - j.val) : Nat) : ℝ)) ^ 2 =
      (((j.val + 1) * (m - j.val) : Nat) : ℝ) := by
  exact Real.sq_sqrt (Nat.cast_nonneg _)

end Imscribing.Paraconsistent.TensorFiltration
