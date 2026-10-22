import Imscribing.Paraconsistent.SourceBoundSplit
import Imscribing.PrimeWells
import Imscribing.Paraconsistent.CongruenceSelection

namespace Imscribing.Paraconsistent.SourceBoundSelection

open SourceBoundSplit

def artifactId : String := "40f40015f1de4741a30c54c148163150"
def word : String := "⊢⊙∈⊤≻⋈⊤⊥≺⊥≻⋈⊞⊙∋⊡⊣"
def ops : Array Op := #[.vinit,.imscrib,.fsplit,.evalt,.afwd,.clink,.evalt,
  .evalf,.arev,.evalf,.afwd,.clink,.engagr,.imscrib,.ffuse,.ifix,.tanch]
def wires : Array Wire := #[⟨3,false,4⟩,⟨4,false,5⟩,⟨5,false,6⟩,⟨2,true,3⟩,
  ⟨6,false,14⟩,⟨7,false,8⟩,⟨8,false,9⟩,⟨9,false,10⟩,⟨10,false,11⟩,
  ⟨11,false,12⟩,⟨12,false,13⟩,⟨2,false,7⟩,⟨13,false,14⟩,
  ⟨0,false,1⟩,⟨1,false,2⟩,⟨14,false,15⟩,⟨15,false,16⟩]
def expectedInputs : List Nat := [0,15,15,5,5,5,5,10,10,5,0,0,0,12,13,13,13]

/-- The register walk used by `cycle` is separate from graph edge flow.
Keep its frame stack and fixation when retaining each cut's landing. -/
structure CutWalk where
  reg : Reg16_3 := Imscribing.IUTT.empty
  frames : List Reg16_3 := []
  fixed : Bool := false

def touch (w : CutWalk) (value : Reg16_3) : CutWalk :=
  {w with reg:=w.reg.union value,frames:=match w.frames with
    | [] => []
    | f::rest => f.union value::rest}

def walkStep (w : CutWalk) (op : Op) : CutWalk :=
  if w.fixed && op != .ifix && op != .imscrib then w else
  match op with
  | .vinit => {}
  | .afwd | .imscrib => if mask w.reg == 0 then {w with reg:=⟨true,false,false,false⟩} else w
  | .arev => {w with reg:=Imscribing.IUTT.empty}
  | .fsplit => {w with frames:=Imscribing.IUTT.empty::w.frames}
  | .ffuse => match w.frames with
    | [] => w
    | f::rest => {w with reg:=w.reg.union f,frames:=match rest with
      | [] => []
      | parent::tail => parent.union f::tail}
  | .evalt => touch w ⟨true,false,false,false⟩
  | .evalf => touch w ⟨false,true,false,false⟩
  | .engagr => touch w ⟨false,false,true,true⟩
  | .ifix => {w with fixed:=true}
  | _ => w

def cutLandings : List (Nat × Nat) :=
  (List.range ops.size).map fun cut =>
    let returned := (List.range ops.size).foldl
      (fun w i => walkStep w ops[(i+cut)%ops.size]!) ({} : CutWalk)
    (cut,mask returned.reg)

/-- The original returned carrier stays inside every selection continuation.
Point banks are appended at executed boundaries, never during failed attempts. -/
structure State (N : Nat) where
  carrier : SourceBoundSplit.State N
  usePrimeWell : Bool := true
  useCongruence : Bool := false
  congruence : CongruenceSelection.State := {}
  primeWell : Option PrimeWells.WellAddress := none
  primeSearch : PrimeWells.Search N := PrimeWells.startSearch N
  wellRemainder : Nat := N
  phaseCuts : List (Nat × Nat) := cutLandings
  /-- Next positive multiple k in E(E-1)=kN. -/
  cursor : Nat := 1
  attempts : Nat := 0
  selected : Option Nat := none
  complement : Option Nat := none
  truthFactor : Option Nat := none
  truthQuotient : Option Nat := none
  falseFactor : Option Nat := none
  falseQuotient : Option Nat := none
  pointBanks : List (Nat × Nat) := []
  edges : Array Reg16_3 := Array.replicate wires.size Imscribing.IUTT.empty
  nodeInputs : List Nat := []
  pc : Nat := 0
  fused : Bool := false
  fixed : Bool := false
  failure : Option String := none
  deriving DecidableEq

instance (N : Nat) : Repr (State N) where
  reprPrec s _ := "selection(pc=" ++ repr s.pc ++ ", cursor=" ++ repr s.cursor ++
    ", attempts=" ++ repr s.attempts ++ ", selected=" ++ repr s.selected ++ ")"

def prepare {N} (carrier : SourceBoundSplit.State N) (usePrimeWell : Bool := true)
    (useCongruence : Bool := false) : State N :=
  {carrier:=carrier,usePrimeWell:=usePrimeWell,useCongruence:=useCongruence,
   congruence:=if useCongruence then CongruenceSelection.prepare N else {},
   primeWell:=if usePrimeWell && !useCongruence then some PrimeWells.origin else none}

def finished {N} (s : State N) : Bool := s.failure.isSome || s.pc ≥ ops.size

def step {N} (s : State N) : State N := Id.run do
  if finished s then return s
  if !s.carrier.fused || s.carrier.observation.isNone ||
      !s.carrier.openFrames.isEmpty || binEval s.carrier.sourceWell != N then
    return {s with failure:=some "selection lost its returned source carrier"}
  let node := s.pc
  -- Selection belongs to the first T gate. The Prime Well owns a retained
  -- entrance search; the archived residual-level mode uses an exact root.
  -- Both return their point through the same fixed complex carrier.
  let discriminant := if s.usePrimeWell || s.useCongruence then 0 else 1+4*s.cursor*N
  let root := Nat.sqrt discriminant
  let mut candidate := (root+1)/2
  let mut s := s
  if node == 3 && s.selected.isNone && s.useCongruence then
    let next := CongruenceSelection.step N s.congruence
    s := {s with congruence:=next,attempts:=s.attempts+1}
    if let some failure := next.failure then return {s with failure:=some failure}
    let some d := next.divisor | return s
    if !CongruenceSelection.proper N d then
      return {s with failure:=some "congruence producer returned an improper divisor"}
    let q := N/d
    if Nat.gcd d q != 1 then
      return {s with failure:=some "congruence split has no complementary idempotent"}
    candidate := (q * ((q : ZMod d)⁻¹).val) % N
  if node == 3 && s.selected.isNone && s.usePrimeWell && !s.useCongruence then
    match PrimeWells.searchStep s.primeSearch with
    | .held next =>
      return {s with primeSearch:=next,attempts:=s.attempts+1}
    | .entered p prime divides =>
      if p ≥ N then return {s with failure:=some "Prime Well has no proper coordinate split"}
      let address := PrimeWells.enter p prime
      let q := N/p
      if PrimeWells.value address*q != N then
        return {s with failure:=some "Prime Well partial address lost its source product"}
      s := {s with primeWell:=some address,wellRemainder:=q}
      if Nat.gcd p q != 1 then
        return {s with failure:=some "Prime Well split has no complementary idempotent"}
      candidate := (q * ((q : ZMod p)⁻¹).val) % N
  if node == 3 && s.selected.isNone then
    if s.cursor ≥ N then
      return {s with failure:=some "zero fibre exhausted without a supported proper divisor"}
    if (!s.usePrimeWell && !s.useCongruence && root*root != discriminant) || candidate ≤ 1 || candidate ≥ N then
      return {s with cursor:=s.cursor+1,attempts:=s.attempts+1}
    let e : ZMod N := candidate
    if e*e != e then return {s with cursor:=s.cursor+1,attempts:=s.attempts+1}
    if (readDivisorAt s.carrier e).isNone then
      return {s with cursor:=s.cursor+1,attempts:=s.attempts+1}
  let op := ops[node]!
  let mut input := Imscribing.IUTT.empty
  for i in [:wires.size] do
    if wires[i]!.target == node then input := input.union s.edges[i]!
  s := {s with nodeInputs:=s.nodeInputs ++ [mask input]}
  if node == 3 then
    s := {s with selected:=some candidate,attempts:=s.attempts+1,pointBanks:=s.pointBanks ++ [(node,candidate)]}
  if node == 4 then
    let some e := s.selected | return {s with failure:=some "T arm lacks its selected point"}
    let some d := readDivisorAt s.carrier (e : ZMod N) |
      return {s with failure:=some "T arm failed the supported divisor boundary"}
    s := {s with truthFactor:=some d}
  if node == 5 then
    let some d := s.truthFactor | return {s with failure:=some "T gcd missing"}
    s := {s with truthQuotient:=some (N/d)}
  if node == 6 then
    let some d := s.truthFactor | return {s with failure:=some "proper-divisor observation missing"}
    if !(1 < d && d < N) then return {s with failure:=some "improper divisor"}
  if node == 7 then
    let some d := s.truthFactor | return {s with failure:=some "remainder observation missing"}
    if N%d != 0 then return {s with failure:=some "nonzero remainder"}
  if node == 8 then
    let some e := s.selected | return {s with failure:=some "parity input missing"}
    let other := ((1 : ZMod N)-(e : ZMod N)).val
    s := {s with complement:=some other,pointBanks:=s.pointBanks ++ [(node,other)]}
  if node == 9 then
    -- The native EVALF input is Tt here. Retrieve the numerical parity point
    -- from its enclosing bank even though the control register projects to N.
    let some other := s.complement | return {s with failure:=some "parity bank missing"}
    if s.pointBanks.getLast? != some (8,other) then
      return {s with failure:=some "parity point changed across EVALF"}
  if node == 10 then
    let some other := s.complement | return {s with failure:=some "F point missing"}
    let some d := readDivisorAt s.carrier (other : ZMod N) |
      return {s with failure:=some "F arm failed the supported divisor boundary"}
    s := {s with falseFactor:=some d}
  if node == 11 then
    let some d := s.falseFactor | return {s with failure:=some "F gcd missing"}
    s := {s with falseQuotient:=some (N/d)}
  if node == 14 then
    let some d := s.truthFactor | return {s with failure:=some "fuse lacks T factor"}
    let some q := s.truthQuotient | return {s with failure:=some "fuse lacks quotient"}
    if s.falseFactor != some q || s.falseQuotient != some d || d*q != N then
      return {s with failure:=some "correlated product boundary did not close"}
    s := {s with fused:=true}
  if node == 15 then
    if !s.fused then return {s with failure:=some "factor fixation preceded fusion"}
    s := {s with fixed:=true}
  if node == 16 && !s.fixed then return {s with failure:=some "unfixed factor return"}
  let mut edges := s.edges
  for i in [:wires.size] do
    if wires[i]!.source == node then edges := edges.set! i (flagOut op input wires[i]!.port)
  return {s with edges:=edges,pc:=node+1}

end Imscribing.Paraconsistent.SourceBoundSelection
