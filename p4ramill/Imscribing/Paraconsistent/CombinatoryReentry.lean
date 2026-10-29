import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.FullyNestedFactorMachine
import Imscribing.Paraconsistent.MultiplicativeReentry
import Imscribing.Paraconsistent.SourceBoundSplit
import Imscribing.Paraconsistent.SourceBoundSelection

/-!
S/K/I programs with native SIXTEEN_3 data. Bracket abstraction compiles a
variable out of a term and is verified by reduction. A certified reducer
executes finite prefixes of unrestricted combinatory recursion. Native
negation and all six lattice operations execute on the fork's carrier.
Composition joins programs by certified reduction.
-/

namespace Imscribing.Paraconsistent.CombinatoryReentry

open Temporal.Semantics

/-- The fork's join and meet operations in each of its three native orders. -/
inductive LatticeOp where
  | joinInformation | meetInformation
  | joinTruth | meetTruth
  | joinFalsity | meetFalsity
  deriving DecidableEq, Repr

def LatticeOp.apply : LatticeOp → Lean.Sixteen3 → Lean.Sixteen3 → Lean.Sixteen3
  | .joinInformation => Lean.Sixteen3.join_i
  | .meetInformation => Lean.Sixteen3.meet_i
  | .joinTruth => Lean.Sixteen3.join_t
  | .meetTruth => Lean.Sixteen3.meet_t
  | .joinFalsity => Lean.Sixteen3.join_f
  | .meetFalsity => Lean.Sixteen3.meet_f

/-- Divisibility evidence retains an independent contradictory falsity pole. -/
def divisorEvidence (N k : Nat) (contradictory : Bool := false) : Lean.Sixteen3 :=
  if k ∣ N then
    if contradictory then ⟨false, false, false, true⟩ else ⟨false, true, false, false⟩
  else ⟨false, false, true, false⟩

def acceptsDivisor (N k : Nat) (contradictory : Bool) : Bool :=
  Lean.Sixteen3.assertsTrue (divisorEvidence N k contradictory)

inductive Term where
  | sourceSelect : Term
  | selectionState : (N : Nat) → SourceBoundSelection.State N → Term
  | sourceSplit : Term
  | sourceState : (N : Nat) → SourceBoundSplit.State N → Term
  | multiplicativeSplit : Nat → Term
  | productFamily : Nat → MultiplicativeReentry.Family → Term
  | number : Nat → Term
  | numbers : List Nat → Term
  | divisor : Nat → Bool → Term
  | divisors : Nat → Bool → Term
  | divisorScan : Nat → Bool → Nat → Term
  | divisorsScan : Nat → Bool → Nat → List Nat → Term
  | nestedFactor : Nat → Term
  | nestedFactorScan : Nat → Nat → Term
  | residentFactor : Nat → Nat → Term
  | residentFactorScan : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Term
  | var : Nat → Term
  | i | k | s
  | datum : Lean.Sixteen3 → Term
  | negation | informationJoin
  | lattice : LatticeOp → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

local infixl:70 " @@ " => Term.app

/-- Normalize identity wrappers captured by call-by-name self application.
The Y operator and all source-carrying payloads remain in the term. -/
def stripIdentities : Term → Term
  | .app f x => if f = .i then stripIdentities x else stripIdentities f @@ stripIdentities x
  | t => t

def sourceSelectBody (self : Term) (N : Nat) (state : SourceBoundSelection.State N) : Term :=
  if SourceBoundSelection.finished state then .selectionState N state
  else stripIdentities self @@ .selectionState N (SourceBoundSelection.step state)

/-- The certified Y continuation acts on the entire correlated source carrier. -/
def sourceSplitBody (self : Term) (N : Nat) (state : SourceBoundSplit.State N) : Term :=
  if state.failure.isSome || state.pc ≥ SourceBoundSplit.ops.size then .sourceState N state
  else self @@ .sourceState N (SourceBoundSplit.step state)

/-- Re-entry transforms the complete paired family and returns through the
same Y continuation. The source product is the readout boundary. -/
def multiplicativeBody (N : Nat) (self : Term) (modulus : Nat)
    (family : MultiplicativeReentry.Family) : Term :=
  match MultiplicativeReentry.read N family with
  | some d => .number d
  | none =>
    if family = ∅ ∨ N < modulus then .numbers []
    else self @@ .productFamily (2*modulus)
      (MultiplicativeReentry.reenter N modulus family)

/-- The existing paired square machine on arbitrary-precision retained state. -/
def nestedFactorBody (N a : Nat) : Term :=
  match FullyNestedFactorMachine.stepNat N a with
  | some d => .number d
  | none => .nestedFactorScan N (a + 1)

/-- The recovered dialectic's source, residual, multiplier and cell remain in
one compact return. The support mask is prepared by the existing Lean program. -/
def residentFactorStart (N mask : Nat) : Term :=
  let a := FullyNestedFactorMachine.initialNat N
  .residentFactorScan N mask 0 N a (a*a-N) 0

def residentFactorBody (N mask k source a residual cell : Nat) : Term := Id.run do
  if mask.testBit (residual % 256) then
    let b := Nat.sqrt residual
    if b*b == residual then
      for candidate in [a+b, a-b] do
        let d := Nat.gcd candidate N
        if 1 < d && d < N && N % d == 0 then return .number d
  let limit := if k == 0 then 4096 else 64
  if cell+1 < limit then
    return .residentFactorScan N mask k source (a+1) (residual+2*a+1) (cell+1)
  let nextSource := if k == 0 then 4*N else source+4*N
  let nextA := FullyNestedFactorMachine.initialNat nextSource
  return .residentFactorScan N mask (k+1) nextSource nextA (nextA*nextA-nextSource) 0

/-- One unfolding of the requested factor functional. -/
def factorBody (N : Nat) (contradictory : Bool) (self : Term) (k : Nat) : Term :=
  if k ≥ N then .number N
  else if 1 < k ∧ acceptsDivisor N k contradictory = true then .number k
  else self @@ .number (k + 1)

/-- The accumulator carries every designated nontrivial divisor. -/
def factorsBody (N : Nat) (contradictory : Bool) (self : Term)
    (k : Nat) (acc : List Nat) : Term :=
  if k ≥ N then .numbers acc
  else self @@ .number (k + 1) @@ .numbers
    (if 1 < k ∧ acceptsDivisor N k contradictory = true then k :: acc else acc)

/-- Compact tail states keep Y re-entry from rebuilding its combinator spine. -/
def divisorScanBody (N : Nat) (contradictory : Bool) (k : Nat) : Term :=
  if k ≥ N then .number N
  else if 1 < k ∧ acceptsDivisor N k contradictory = true then .number k
  else .divisorScan N contradictory (k + 1)

def divisorsScanBody (N : Nat) (contradictory : Bool) (k : Nat)
    (acc : List Nat) : Term :=
  if k ≥ N then .numbers acc
  else .divisorsScan N contradictory (k + 1)
    (if 1 < k ∧ acceptsDivisor N k contradictory = true then k :: acc else acc)

/-- Combinator contraction and reduction inside either application arm. -/
inductive Step : Term → Term → Prop where
  | sourceSelect (self N state) :
      Step (.sourceSelect @@ self @@ .selectionState N state) (sourceSelectBody self N state)
  | sourceSplit (self N state) :
      Step (.sourceSplit @@ self @@ .sourceState N state) (sourceSplitBody self N state)
  | multiplicativeSplit (N self modulus family) :
      Step (.multiplicativeSplit N @@ self @@ .productFamily modulus family)
        (multiplicativeBody N self modulus family)
  | residentFactorStart (N mask self payload) :
      Step (.residentFactor N mask @@ self @@ payload) (residentFactorStart N mask)
  | residentFactorScan (N mask k source a residual cell) :
      Step (.residentFactorScan N mask k source a residual cell)
        (residentFactorBody N mask k source a residual cell)
  | nestedFactorStart (N self a) :
      Step (.nestedFactor N @@ self @@ .number a) (.nestedFactorScan N a)
  | nestedFactorScan (N a) :
      Step (.nestedFactorScan N a) (nestedFactorBody N a)
  | factor (N contradictory self k) :
      Step (.divisor N contradictory @@ self @@ .number k)
        (factorBody N contradictory self k)
  | factors (N contradictory self k acc) :
      Step (.divisors N contradictory @@ self @@ .number k @@ .numbers acc)
        (factorsBody N contradictory self k acc)
  | divisorStart (N contradictory self k) :
      Step (.divisor N contradictory @@ self @@ .number k)
        (.divisorScan N contradictory k)
  | divisorScan (N contradictory k) :
      Step (.divisorScan N contradictory k)
        (divisorScanBody N contradictory k)
  | divisorsStart (N contradictory self k acc) :
      Step (.divisors N contradictory @@ self @@ .number k @@ .numbers acc)
        (.divisorsScan N contradictory k acc)
  | divisorsScan (N contradictory k acc) :
      Step (.divisorsScan N contradictory k acc)
        (divisorsScanBody N contradictory k acc)
  | identity (x) : Step (.i @@ x) x
  | constant (x y) : Step (.k @@ x @@ y) x
  | substitution (f g x) : Step (.s @@ f @@ g @@ x) (f @@ x @@ (g @@ x))
  | negation (x) : Step (.negation @@ .datum x) (.datum (FDE.liftNegation x))
  | informationJoin (x y) :
      Step (.informationJoin @@ .datum x @@ .datum y)
        (.datum (Lean.Sixteen3.join_i x y))
  | lattice (op x y) :
      Step (.lattice op @@ .datum x @@ .datum y) (.datum (op.apply x y))
  | left {f g} (h : Step f g) (x) : Step (f @@ x) (g @@ x)
  | right (f) {x y} (h : Step x y) : Step (f @@ x) (f @@ y)

/-- A finite sequence of zero or more certified reduction steps. -/
inductive Steps : Term → Term → Prop where
  | refl (t) : Steps t t
  | cons {a b c} : Step a b → Steps b c → Steps a c

theorem Steps.single {a b} (h : Step a b) : Steps a b :=
  .cons h (.refl b)

theorem Steps.trans {a b c} (h : Steps a b) (g : Steps b c) : Steps a c :=
  match h with
  | .refl _ => g
  | .cons step tail => .cons step (tail.trans g)

theorem Steps.left {a b} (h : Steps a b) (x) : Steps (a @@ x) (b @@ x) :=
  match h with
  | .refl _ => .refl _
  | .cons step tail => .cons (.left step x) (tail.left x)

theorem Steps.right (f) {a b} (h : Steps a b) : Steps (f @@ a) (f @@ b) :=
  match h with
  | .refl _ => .refl _
  | .cons step tail => .cons (.right f step) (tail.right f)

/-- Captured-self normalization consists only of valid identity contractions
and reductions under application. It introduces no new arithmetic rule. -/
theorem stripIdentities_reduces (t : Term) : Steps t (stripIdentities t) := by
  induction t with
  | app f x ihf ihx =>
    change Steps (f @@ x) (if f = .i then stripIdentities x else stripIdentities f @@ stripIdentities x)
    split_ifs with h
    · subst f
      exact (Steps.single (Step.identity x)).trans ihx
    · exact (ihf.left x).trans (Steps.right _ ihx)
  | _ => exact .refl _

/-- Substitution into combinatory syntax has no binders to capture variables. -/
def subst (target : Nat) (replacement : Term) : Term → Term
  | .var name => if name = target then replacement else .var name
  | .app f x => subst target replacement f @@ subst target replacement x
  | t => t

/-- Bracket abstraction compiles a variable out using only S, K, and I. -/
def abstract (target : Nat) : Term → Term
  | .var name => if name = target then .i else .k @@ .var name
  | .app f x => .s @@ abstract target f @@ abstract target x
  | t => .k @@ t

/-- The abstraction compiler implements substitution for every body and argument. -/
theorem abstract_apply (target : Nat) (argument body : Term) :
    Steps (abstract target body @@ argument) (subst target argument body) := by
  induction body with
  | var name =>
      by_cases h : name = target
      · simpa only [abstract, subst, if_pos h] using
          Steps.single (Step.identity argument)
      · simpa only [abstract, subst, if_neg h] using
          Steps.single (Step.constant (.var name) argument)
  | app f x ihf ihx =>
      exact (Steps.single (Step.substitution _ _ argument)).trans
        ((ihf.left _).trans (Steps.right _ ihx))
  | sourceSplit => exact Steps.single (Step.constant .sourceSplit argument)
  | sourceSelect => exact Steps.single (Step.constant .sourceSelect argument)
  | selectionState n state => exact Steps.single (Step.constant (.selectionState n state) argument)
  | sourceState n state => exact Steps.single (Step.constant (.sourceState n state) argument)
  | multiplicativeSplit n => exact Steps.single (Step.constant (.multiplicativeSplit n) argument)
  | productFamily modulus family => exact Steps.single (Step.constant (.productFamily modulus family) argument)
  | number n => exact Steps.single (Step.constant (.number n) argument)
  | numbers ns => exact Steps.single (Step.constant (.numbers ns) argument)
  | divisor n b => exact Steps.single (Step.constant (.divisor n b) argument)
  | divisors n b => exact Steps.single (Step.constant (.divisors n b) argument)
  | divisorScan n b k => exact Steps.single (Step.constant (.divisorScan n b k) argument)
  | divisorsScan n b k acc => exact Steps.single (Step.constant (.divisorsScan n b k acc) argument)
  | nestedFactor n => exact Steps.single (Step.constant (.nestedFactor n) argument)
  | nestedFactorScan n a => exact Steps.single (Step.constant (.nestedFactorScan n a) argument)
  | residentFactor n mask => exact Steps.single (Step.constant (.residentFactor n mask) argument)
  | residentFactorScan n mask k source a residual cell =>
      exact Steps.single (Step.constant (.residentFactorScan n mask k source a residual cell) argument)
  | i => exact Steps.single (Step.constant .i argument)
  | k => exact Steps.single (Step.constant .k argument)
  | s => exact Steps.single (Step.constant .s argument)
  | datum x => exact Steps.single (Step.constant (.datum x) argument)
  | negation => exact Steps.single (Step.constant .negation argument)
  | informationJoin => exact Steps.single (Step.constant .informationJoin argument)
  | lattice op => exact Steps.single (Step.constant (.lattice op) argument)

theorem lattice_apply (op : LatticeOp) (x y : Lean.Sixteen3) :
    Steps (.lattice op @@ .datum x @@ .datum y) (.datum (op.apply x y)) :=
  Steps.single (.lattice op x y)

/-- Compose an outer program with an inner program using S and K. -/
def after (outer inner : Term) : Term := .s @@ (.k @@ outer) @@ inner

theorem after_unfold (outer inner argument : Term) :
    Steps (after outer inner @@ argument) (outer @@ (inner @@ argument)) :=
  .cons (.substitution (.k @@ outer) inner argument)
    (.cons (.left (.constant outer argument) (inner @@ argument)) (.refl _))

theorem after_apply (outer inner : Term) (x y z : Lean.Sixteen3)
    (hinner : Steps (inner @@ .datum x) (.datum y))
    (houter : Steps (outer @@ .datum y) (.datum z)) :
    Steps (after outer inner @@ .datum x) (.datum z) :=
  (after_unfold outer inner (.datum x)).trans ((Steps.right outer hinner).trans houter)

def duplicate : Term := .s @@ .i @@ .i

theorem duplicate_apply (x : Term) : Steps (duplicate @@ x) (x @@ x) :=
  .cons (.substitution .i .i x)
    (.cons (.left (.identity x) (.i @@ x))
      (.cons (.right x (.identity x)) (.refl _)))

theorem SKK_identity (x : Term) : Steps (.s @@ .k @@ .k @@ x) x :=
  .cons (.substitution .k .k x)
    (.cons (.constant x (.k @@ x)) (.refl _))

def recursiveHalf (f : Term) : Term := .s @@ (.k @@ f) @@ duplicate

def unfoldState (f : Term) : Term := recursiveHalf f @@ recursiveHalf f

/-- Curry Y generated by the verified abstraction compiler. -/
def Y : Term := abstract 0 (unfoldState (.var 0))

theorem recursiveHalf_apply (f x : Term) :
    Steps (recursiveHalf f @@ x) (f @@ (x @@ x)) :=
  .cons (.substitution (.k @@ f) duplicate x)
    (.cons (.left (.constant f x) (duplicate @@ x))
      (Steps.right f (duplicate_apply x)))

theorem Y_first_steps (f : Term) : Steps (Y @@ f) (unfoldState f) :=
  abstract_apply 0 f (unfoldState (.var 0))

theorem Y_unfolds (f : Term) :
    Steps (Y @@ f) (f @@ unfoldState f) :=
  (Y_first_steps f).trans (recursiveHalf_apply f (recursiveHalf f))

/-- Equality generated by reduction, its converse, and transitivity. -/
inductive Conversion : Term → Term → Prop where
  | reduce {a b} : Steps a b → Conversion a b
  | symm {a b} : Conversion a b → Conversion b a
  | trans {a b c} : Conversion a b → Conversion b c → Conversion a c

/-- The unrestricted Y equation in combinatory conversion. -/
theorem Y_fixedpoint (f : Term) : Conversion (Y @@ f) (f @@ (Y @@ f)) :=
  .trans (.reduce (Y_unfolds f))
    (.symm (.reduce (Steps.right f (Y_first_steps f))))

/-- Constant recursive functionals compute their result through Y. -/
theorem Y_constant (x : Term) : Steps (Y @@ (.k @@ x)) x :=
  (Y_unfolds (.k @@ x)).trans
    (Steps.single (.constant x (unfoldState (.k @@ x))))

/-- S duplicates an observation between native join and negation. -/
def hold : Term := .s @@ .informationJoin @@ .negation

theorem hold_apply (x : Lean.Sixteen3) :
    Steps (hold @@ .datum x) (.datum (FDE.negationClosure x)) :=
  .cons (.substitution .informationJoin .negation (.datum x))
    (.cons (.right (.informationJoin @@ .datum x) (.negation x))
      (.cons (.informationJoin x (FDE.liftNegation x)) (.refl _)))

/-- Compile the retained-seed negation map as a combinator program. -/
def seededOperator (seed : Lean.Sixteen3) : Term :=
  abstract 0 (.informationJoin @@ (.negation @@ .var 0) @@ .datum seed)

theorem seededOperator_apply (seed x : Lean.Sixteen3) :
    Steps (seededOperator seed @@ .datum x)
      (.datum (FDE.negationSeededStep seed x)) :=
  (abstract_apply 0 (.datum x)
      (.informationJoin @@ (.negation @@ .var 0) @@ .datum seed)).trans
    (.cons (.left (.right .informationJoin (.negation x)) (.datum seed))
      (.cons (.informationJoin (FDE.liftNegation x) seed) (.refl _)))

/-- Every returned contraction carries its reduction proof. -/
def rootStep : (t : Term) → Option {u : Term // Step t u}
  | .app (.app .sourceSelect self) (.selectionState N state) =>
      some ⟨sourceSelectBody self N state, .sourceSelect self N state⟩
  | .app (.app .sourceSplit self) (.sourceState N state) =>
      some ⟨sourceSplitBody self N state, .sourceSplit self N state⟩
  | .app (.app (.multiplicativeSplit N) self) (.productFamily modulus family) =>
      some ⟨multiplicativeBody N self modulus family,
        .multiplicativeSplit N self modulus family⟩
  | .app (.app (.residentFactor N mask) self) payload =>
      some ⟨residentFactorStart N mask, .residentFactorStart N mask self payload⟩
  | .residentFactorScan N mask k source a residual cell =>
      some ⟨residentFactorBody N mask k source a residual cell,
        .residentFactorScan N mask k source a residual cell⟩
  | .app (.app (.nestedFactor N) self) (.number a) =>
      some ⟨.nestedFactorScan N a, .nestedFactorStart N self a⟩
  | .nestedFactorScan N a => some ⟨nestedFactorBody N a, .nestedFactorScan N a⟩
  | .app (.app (.divisor N b) self) (.number k) =>
      some ⟨.divisorScan N b k, .divisorStart N b self k⟩
  | .app (.app (.app (.divisors N b) self) (.number k)) (.numbers acc) =>
      some ⟨.divisorsScan N b k acc, .divisorsStart N b self k acc⟩
  | .divisorScan N b k => some ⟨divisorScanBody N b k, .divisorScan N b k⟩
  | .divisorsScan N b k acc =>
      some ⟨divisorsScanBody N b k acc, .divisorsScan N b k acc⟩
  | .app .i x => some ⟨x, .identity x⟩
  | .app (.app .k x) y => some ⟨x, .constant x y⟩
  | .app (.app (.app .s f) g) x =>
      some ⟨f @@ x @@ (g @@ x), .substitution f g x⟩
  | .app .negation (.datum x) => some ⟨.datum (FDE.liftNegation x), .negation x⟩
  | .app (.app .informationJoin (.datum x)) (.datum y) =>
      some ⟨.datum (Lean.Sixteen3.join_i x y), .informationJoin x y⟩
  | .app (.app (.lattice op) (.datum x)) (.datum y) =>
      some ⟨.datum (op.apply x y), .lattice op x y⟩
  | _ => none

/-- Contract the first available redex, visiting the left arm before the right. -/
def reduceOnce : (t : Term) → Option {u : Term // Step t u}
  | .app f x =>
      match rootStep (.app f x) with
      | some result => some result
      | none =>
          match reduceOnce f with
          | some result => some ⟨result.val @@ x, .left result.property x⟩
          | none =>
              match reduceOnce x with
              | some result => some ⟨f @@ result.val, .right f result.property⟩
              | none => none
  | t => rootStep t

/-- Execute a finite prefix; a term with no next contraction is retained. -/
def run : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
      match reduceOnce t with
      | some result => run fuel result.val
      | none => t

theorem run_reduces (fuel : Nat) (t : Term) : Steps t (run fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl t
  | succ fuel ih =>
      cases h : reduceOnce t with
      | none => simpa only [run, h] using Steps.refl t
      | some result =>
          simpa only [run, h] using Steps.cons result.property (ih result.val)

theorem run_halted (fuel : Nat) (t : Term) (h : reduceOnce t = none) :
    run fuel t = t := by
  cases fuel <;> simp only [run, h]

/-- Splitting the fuel budget pauses and resumes the same execution. -/
theorem run_add (first second : Nat) (t : Term) :
    run (first + second) t = run second (run first t) := by
  induction first generalizing t with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
      cases h : reduceOnce t with
      | none => simp only [Nat.succ_add, run, h, run_halted second t h]
      | some result =>
          simpa only [Nat.succ_add, run, h] using ih result.val

/-- A computable signal exposes every successive combinator reduction. -/
def executionSignal (t : Term) : Signal Term := fun tick => run tick t

theorem executionSignal_tick (t : Term) (tick : Nat) :
    executionSignal t (tick + 1) = executionSignal t tick ∨
      Step (executionSignal t tick) (executionSignal t (tick + 1)) := by
  change run (tick + 1) t = run tick t ∨ Step (run tick t) (run (tick + 1) t)
  rw [run_add tick 1 t]
  cases h : reduceOnce (run tick t) with
  | none => exact Or.inl (run_halted 1 _ h)
  | some result =>
      exact Or.inr (by simpa only [run, h] using result.property)

end Imscribing.Paraconsistent.CombinatoryReentry
