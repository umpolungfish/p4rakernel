import Imscribing.Paraconsistent.LeanOnlyMembrane

open Imscribing.Paraconsistent.LeanOnlyMembrane
open Imscribing.Paraconsistent.CombinatoryReentry

/-- Exact source from the retained integration receipt. No reference factors. -/
def lockedSource : Nat := 412023436986659543855531365332575948179811699844327982845455626433876445565248426198098870423161841879261420247188869492560931776375033421130982397485150944909106910269861031862704114880866970564902903653658867433731720813104105190864254793282601391257624033946373269391

/-- Execute the existing Y to its resident primitive call. The primitive uses
the actual minimum-prime-coordinate operation consumed by primeFactorsList. -/
partial def primeWellReturn (source : Nat) (term : Term) : IO Unit := do
  match term with
  | .app (.app (.var 37) _) (.number n) =>
    unless n == source do throw (IO.userError "Y source boundary changed")
    let d := Nat.minFac n
    unless 1 < d && d < n && n % d == 0 && d*(n/d) == source do
      throw (IO.userError "prime well did not return a proper divisor")
    IO.println s!"factor={d} quotient={n/d} remainder={n%d} product={d*(n/d)}"
  | _ =>
    match reduceOnce term with
    | some next => primeWellReturn source next.val
    | none => throw (IO.userError "Y halted before its prime-well operation")

def primeWell (n : Nat) : IO Unit := do
  let well := Nat.digits 2 n
  let source := binEval well
  unless source == n do throw (IO.userError "binary-well source recovery failed")
  primeWellReturn n (.app (.app Y (.var 37)) (.number source))

partial def runUntil {N : Nat} (deadline : Nat) (m : Membrane N) :
    IO (Membrane N) := do
  if (readFactor m).isSome then return m
  if (← IO.monoNanosNow) ≥ deadline then return m
  runUntil deadline (trigger 1 m)

def boundedSource (N seconds : Nat) : IO Unit := do
  let before ← IO.monoNanosNow
  let m := prepare N
  unless binEval m.sourceWell == N do
    throw (IO.userError "source preparation failed")
  let ready ← IO.monoNanosNow
  let returned ← runUntil (ready + seconds * 1000000000) m
  report returned
  let finished ← IO.monoNanosNow
  IO.println s!"preparation_ns={ready-before} trigger_to_readout_ns={finished-ready}"

def execute (N fuel : Nat) : IO Unit := do
  let before ← IO.monoNanosNow
  let m := prepare N
  -- Force source preparation before starting the trigger clock.
  unless binEval m.sourceWell == N do throw (IO.userError "source preparation failed")
  let ready ← IO.monoNanosNow
  let returned := trigger fuel m
  report returned
  let finished ← IO.monoNanosNow
  IO.println s!"preparation_ns={ready-before} trigger_to_readout_ns={finished-ready}"

def sourceProgram (N : Nat) : Term :=
  .app (.app Y .sourceSplit) (.sourceState N (Imscribing.Paraconsistent.SourceBoundSplit.prepare N))

open Imscribing.Paraconsistent.SourceBoundSplit in
def sourceProtocol (N : Nat) : IO Unit := do
  let started ← IO.monoNanosNow
  unless N ≥ 2^199 do throw (IO.userError "source requires at least 200 bits")
  let program := sourceProgram N
  let returned := run 4096 program
  have reduction : Steps program returned := run_reduces 4096 program
  let _ := reduction
  match returned with
  | .sourceState source state =>
    unless source == N && binEval state.sourceWell == N do
      throw (IO.userError "source boundary changed")
    if let some failure := state.failure then throw (IO.userError failure)
    unless state.pc == ops.size && state.fused && state.openFrames.isEmpty do
      throw (IO.userError "source graph did not return a closed membrane")
    unless state.nodeInputs == expectedInputs do
      throw (IO.userError "native node flow differs from the supplied graph")
    unless state.banks.head?.map Bank.data == some state.original do
      throw (IO.userError "containing source bank did not return")
    let some observation := state.observation | throw (IO.userError "fixation observation missing")
    unless observation.falsity == state.falsity && observation.truth == state.truth do
      throw (IO.userError "fixed observation changed through fusion")
    unless state.truth.all (fun c => c.residual == Quad.residual source && !c.flipped) do
      throw (IO.userError "truth oracle did not act on the carried coefficients")
    unless state.falsity.all (fun c => c.residual == (Quad.zero source).sub (Quad.residual source) && c.flipped) do
      throw (IO.userError "adjoint/parity did not act on the carried coefficients")
    unless state.joint.length == 8 && state.joint.all (fun c => c.ancestry.isNone) do
      throw (IO.userError "fuse lost charts or retained an uncleared branch tag")
    unless state.clears == 1 && state.banks.any (fun b => b.path == [0,3,8]) do
      throw (IO.userError "nested bank did not carry the reversal")
    IO.println s!"source={N} artifact={artifactId} word={word}"
    IO.println s!"source_bank_return=true native_inputs={state.nodeInputs} Y_reduction_witness=true"
    unless state.joint.all (fun c => c.zeroOnly) do
      throw (IO.userError "fixed residual observation was not retained through fusion")
    IO.println s!"graph_returned=true factor_status=held_zero_fibre charts={state.joint.length} banks={state.banks.length} clears={state.clears} phase_class={observation.phaseClass}"
    let some t := state.truth.head? | throw (IO.userError "truth arm missing")
    let some f := state.falsity.head? | throw (IO.userError "falsity arm missing")
    IO.println s!"T_coefficients={t.residual.c0.val},{t.residual.c1.val},{t.residual.c2.val}"
    IO.println s!"F_coefficients={f.residual.c0.val},{f.residual.c1.val},{f.residual.c2.val} F_parity=true"
    let e : ZMod source := 2
    let r := h e
    unless (List.range 4).all (fun i => amplitudeAt state.joint e r i == 0) do
      throw (IO.userError "fixed zero fibre retained a nonzero residual")
    unless (List.range 4).any (fun i => amplitudeAt state.original e 0 i != 0) do
      throw (IO.userError "zero-fibre fixation destroyed the original source bank")
    unless (readDivisorAt state e).isNone do
      throw (IO.userError "non-idempotent point crossed the factor boundary")
    IO.println s!"T_physical_amplitudes={repr ((List.range 4).map (amplitudeAt state.joint e r))}"
    IO.println s!"F_physical_amplitudes={repr ((List.range 4).map (amplitudeAt state.joint e (-r)))}"
    IO.println s!"phase_cycle_return={observation.phaseCycle.head? == observation.phaseCycle.getLast?} fixed_observation_retained=true"
    IO.println "zero_residual_projection=true original_source_preserved=true selected_nontrivial_point=none"
    IO.println s!"trigger_to_return_ns={(←IO.monoNanosNow)-started}"
  | _ => throw (IO.userError "Y did not return its source-bound carrier")

structure SelectionExecution (initial : Term) where
  continuation : Term
  reduced : Steps initial continuation
  budget : Nat

instance (initial : Term) : Nonempty (SelectionExecution initial) :=
  ⟨⟨initial,.refl initial,0⟩⟩

partial def selectUntil {initial : Term} (deadline : Nat)
    (execution : SelectionExecution initial) : IO (SelectionExecution initial) := do
  match execution.continuation with
  | .selectionState _ _ => return execution
  | _ =>
    if (← IO.monoNanosNow) ≥ deadline then return execution
    selectUntil deadline
      ⟨run 256 execution.continuation,
       execution.reduced.trans (run_reduces 256 execution.continuation),
       execution.budget+256⟩

def selectionPayload : Term → Option ((N : Nat) × Imscribing.Paraconsistent.SourceBoundSelection.State N)
  | .selectionState n s => some ⟨n,s⟩
  | .app f x => (selectionPayload x).orElse (fun _ => selectionPayload f)
  | _ => none

open Imscribing.Paraconsistent.SourceBoundSelection in
def selectionProtocol (N seconds : Nat) (usePrimeWell : Bool := true)
    (useCongruence : Bool := false) : IO Unit := do
  unless N ≥ 2^199 do throw (IO.userError "source requires at least 200 bits")
  let started ← IO.monoNanosNow
  let sourceReturn := run 4096 (sourceProgram N)
  let .sourceState source carrier := sourceReturn |
    throw (IO.userError "source graph did not return its carrier")
  unless source == N && carrier.failure.isNone && carrier.fused do
    throw (IO.userError "source preparation failed")
  let prepared := Imscribing.Paraconsistent.SourceBoundSelection.prepare carrier usePrimeWell useCongruence
  if useCongruence then
    unless prepared.congruence.base.size > 0 do
      throw (IO.userError "congruence preparation produced an empty factor base")
  let program := Term.app (Term.app Y .sourceSelect) (.selectionState source prepared)
  let ready ← IO.monoNanosNow
  let execution ← selectUntil (ready+seconds*1000000000)
    (⟨program,.refl program,0⟩ : SelectionExecution program)
  let returned := execution.continuation
  let readout ← IO.monoNanosNow
  let some ⟨returnedSource,state⟩ := selectionPayload returned |
    throw (IO.userError "selection lost its retained state")
  unless returnedSource == N && binEval state.carrier.sourceWell == N do
    throw (IO.userError "selection source boundary changed")
  if let some failure := state.failure then throw (IO.userError failure)
  IO.println s!"source={N} selection_artifact={artifactId} word={word}"
  IO.println s!"Y_reduction_witness=true reducer_budget={execution.budget}"
  IO.println s!"selection_pc={state.pc} attempts={state.attempts} next_residual_multiple={state.cursor} selected={state.selected}"
  IO.println s!"source_banks={state.carrier.banks.length} phase_observation_retained={state.carrier.observation.isSome} numerical_point_banks={state.pointBanks}"
  if state.useCongruence then
    let c := state.congruence
    IO.println s!"producer=lean-congruence-squares base_size={c.base.size} sieved_positions={c.positions} smooth_relations={c.relations} paired_relations={c.paired} dependencies={c.dependencies} eliminations={c.eliminations} prime_index={c.primeIndex} square_witness={c.witness}"
  if let some address := state.primeWell then
    unless PrimeWells.value address*state.wellRemainder == N do
      throw (IO.userError "partial Prime Well source product changed")
    IO.println s!"prime_well_coordinates={PrimeWells.coordinates address} prime_well_depth={PrimeWells.depth address} prime_well_value={PrimeWells.value address} unresolved_remainder={state.wellRemainder} next_prime_candidate={state.primeSearch.candidate}"
  unless state.phaseCuts == cutLandings do throw (IO.userError "selection lost its cut labels")
  IO.println s!"cycle_cut_landings={state.phaseCuts} native_graph_inputs={state.nodeInputs}"
  if state.fixed && state.pc == ops.size then
    unless state.nodeInputs == expectedInputs do throw (IO.userError "selection native flow mismatch")
    let some d := state.truthFactor | throw (IO.userError "terminal divisor missing")
    let some q := state.truthQuotient | throw (IO.userError "terminal quotient missing")
    unless 1 < d && d < N && N%d == 0 && d*q == N && primeEval [d,q] == N do
      throw (IO.userError "exact terminal product failed")
    let verified ← IO.monoNanosNow
    IO.println s!"factor={d} quotient={q} remainder={N%d} product={d*q} paired_boundary=true prime_well_product=true"
    IO.println s!"trigger_to_verified_factor_ns={verified-ready}"
  else
    IO.println "factor_status=held_selection continuation_retained=true"
  IO.println s!"preparation_ns={ready-started} trigger_to_readout_ns={readout-ready}"

def main (args : List String) : IO Unit := do
  match args with
  | [] => selectionProtocol lockedSource 300 false true
  | ["congruence", seconds] =>
    match seconds.toNat? with
    | some bound => selectionProtocol lockedSource bound false true
    | none => throw (IO.userError "invalid congruence boundary")
  | ["congruence", source, seconds] =>
    match source.toNat?, seconds.toNat? with
    | some n, some bound => selectionProtocol n bound false true
    | _, _ => throw (IO.userError "invalid congruence source or boundary")
  | ["select", seconds] =>
    match seconds.toNat? with
    | some bound => selectionProtocol lockedSource bound false
    | none => throw (IO.userError "invalid selection boundary")
  | ["select", source, seconds] =>
    match source.toNat?, seconds.toNat? with
    | some n, some bound => selectionProtocol n bound false
    | _, _ => throw (IO.userError "invalid source or selection boundary")
  | ["source-split"] => sourceProtocol lockedSource
  | ["source-split", source] =>
    match source.toNat? with
    | some n => sourceProtocol n
    | none => throw (IO.userError "invalid source")
  | ["prime-well"] => selectionProtocol lockedSource 300
  | ["prime-well", source, seconds] =>
    match source.toNat?, seconds.toNat? with
    | some n, some bound => selectionProtocol n bound
    | _, _ => throw (IO.userError "invalid Prime Well source or execution boundary")
  | ["prime-well-control", source] =>
    match source.toNat? with
    | some n =>
      unless n ≥ 2^199 do throw (IO.userError "control requires at least 200 bits")
      selectionProtocol n 300
    | none => throw (IO.userError "invalid source")
  | ["source-bounded", source, seconds] =>
    match source.toNat?, seconds.toNat? with
    | some n, some seconds =>
      unless n ≥ 2^199 do throw (IO.userError "source requires at least 200 bits")
      boundedSource n seconds
    | _, _ => throw (IO.userError "invalid source or execution bound")
  | ["bounded", seconds] =>
    match seconds.toNat? with
    | some n => boundedSource lockedSource n
    | none => throw (IO.userError "invalid execution bound")
  | [fuel] =>
    match fuel.toNat? with
    | some n => execute lockedSource n
    | none => throw (IO.userError "invalid contraction budget")
  | ["control", source, fuel] =>
    match source.toNat?, fuel.toNat? with
    | some n, some steps =>
      unless n ≥ 2^199 do throw (IO.userError "control requires at least 200 bits")
      let m := prepare n
      unless (trigger steps (trigger steps m)).continuation ==
          (trigger (steps+steps) m).continuation do
        throw (IO.userError "retained continuation failed composition")
      IO.println "same_state_resume=true"
      execute n (steps+steps)
    | _, _ => throw (IO.userError "invalid source or contraction budget")
  | _ => throw (IO.userError "usage: lean_only_membrane congruence [N] SECONDS | prime-well [N SECONDS] | select [N] SECONDS | source-split [N] | bounded SECONDS | control N FUEL")
