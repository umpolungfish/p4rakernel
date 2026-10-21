import Imscribing.ReEntryConstructions
import Imscribing.IUTT
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Source-bound reversible residual charts. The coefficients are the executed
state, not a pending arithmetic schedule. Every chart denotes its complete
bounded source family, with its complex amplitudes and ancestry retained. -/
namespace Imscribing.Paraconsistent.SourceBoundSplit

abbrev G := GaussianInt
def imaginary : G := ⟨0, 1⟩

structure Amp where
  a : G
  b : G
  c : G
  d : G
  deriving DecidableEq, Repr

namespace Amp

def add (x y : Amp) : Amp := ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩
def scale (z : G) (x : Amp) : Amp := ⟨z*x.a,z*x.b,z*x.c,z*x.d⟩
def truth (x : Amp) : Amp := ⟨x.a,0,x.c,0⟩
def falsity (x : Amp) : Amp := ⟨0,x.b,0,x.d⟩
def flip (x : Amp) : Amp := ⟨x.b,x.a,x.d,x.c⟩
def get (x : Amp) (i : Nat) : G := if i==0 then x.a else if i==1 then x.b else if i==2 then x.c else x.d

theorem split_fuse (x : Amp) : add (truth x) (falsity x) = x := by
  cases x; simp [add, truth, falsity]

theorem flip_involution (x : Amp) : flip (flip x) = x := rfl

def xp (degree : Nat) (value : G) : G := -imaginary * (degree : G) * value
def px (degree : Nat) (value : G) : G := -imaginary * ((degree : G)+1) * value

theorem commutator (degree : Nat) (value : G) :
    xp degree value - px degree value = imaginary * value := by
  unfold xp px
  ring

/-- Untruncated X(-iD)-(-iD)X, including degree four in the second product. -/
def clink (x : Amp) : Amp :=
  ⟨xp 0 x.a-px 0 x.a, xp 1 x.b-px 1 x.b,
   xp 2 x.c-px 2 x.c, xp 3 x.d-px 3 x.d⟩

theorem clink_eq (x : Amp) : clink x = scale imaginary x := by
  simp [clink, scale, commutator]

end Amp

structure Quad (N : Nat) where
  c0 : ZMod N
  c1 : ZMod N
  c2 : ZMod N
  deriving DecidableEq

namespace Quad

def zero (N : Nat) : Quad N := ⟨0,0,0⟩
def residual (N : Nat) : Quad N := ⟨0,-1,1⟩
def add {N} (x y : Quad N) : Quad N := ⟨x.c0+y.c0,x.c1+y.c1,x.c2+y.c2⟩
def sub {N} (x y : Quad N) : Quad N := ⟨x.c0-y.c0,x.c1-y.c1,x.c2-y.c2⟩
def eval {N} (x : Quad N) (e : ZMod N) : ZMod N := x.c0+x.c1*e+x.c2*e*e

theorem add_sub {N} (x y : Quad N) : sub (add x y) y = x := by
  cases x; cases y; simp [sub, add]

theorem sub_add {N} (x y : Quad N) : add (sub x y) y = x := by
  cases x; cases y; simp [sub, add]

theorem eval_residual (N : Nat) (e : ZMod N) : eval (residual N) e = e*e-e := by
  simp [eval, residual]; ring

theorem eval_add {N} (x y : Quad N) (e : ZMod N) : eval (add x y) e = eval x e+eval y e := by
  simp [eval, add]; ring

theorem eval_sub {N} (x y : Quad N) (e : ZMod N) : eval (sub x y) e = eval x e-eval y e := by
  simp [eval, sub]; ring

end Quad

/-- The same source relation used by the resident idempotent preparation. -/
def h {N : Nat} (e : ZMod N) : ZMod N := e*e-e

def oracle {N : Nat} (point : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (point.1,point.2+h point.1)
def adjoint {N : Nat} (point : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (point.1,point.2-h point.1)

theorem adjoint_forward {N} (point : ZMod N × ZMod N) : adjoint (oracle point) = point := by
  cases point; simp [adjoint, oracle]

theorem forward_adjoint {N} (point : ZMod N × ZMod N) : oracle (adjoint point) = point := by
  cases point; simp [adjoint, oracle]

/-- Direct image and adjoint image are an actual powerset adjunction. -/
theorem source_adjunction (N : Nat) :
    GaloisConnection (Set.image (@oracle N)) (Set.image (@adjoint N)) := by
  intro s t
  constructor
  · intro hs x hx
    exact ⟨oracle x, hs ⟨x,hx,rfl⟩, adjoint_forward x⟩
  · intro hs y hy
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨z,hz,heq⟩ := hs hx
    have eq : oracle x = z := by rw [←heq, forward_adjoint]
    exact eq ▸ hz

theorem parity_residual {N} (e : ZMod N) : h (1-e) = h e := by
  unfold h; ring

structure Chart (N : Nat) where
  sector : Nat
  flipped : Bool
  residual : Quad N
  amplitude : Amp
  ancestry : Option Bool
  deriving DecidableEq

namespace Chart

def point {N} (c : Chart N) (e : ZMod N) : ZMod N := if c.flipped then 1-e else e
def forward {N} (c : Chart N) : Chart N := {c with residual := c.residual.add (Quad.residual N)}
def reverse {N} (c : Chart N) : Chart N := {c with residual := c.residual.sub (Quad.residual N)}
def parity {N} (c : Chart N) : Chart N := {c with flipped := !c.flipped, amplitude := c.amplitude.flip}
def physical {N} (c : Chart N) (e : ZMod N) : ZMod N × ZMod N := (c.point e,c.residual.eval e)

theorem reverse_forward {N} (c : Chart N) : reverse (forward c) = c := by
  cases c; simp [reverse, forward, Quad.add_sub]

theorem forward_reverse {N} (c : Chart N) : forward (reverse c) = c := by
  cases c; simp [reverse, forward, Quad.sub_add]

theorem parity_twice {N} (c : Chart N) : parity (parity c) = c := by
  cases c; simp [parity, Amp.flip_involution]

theorem point_residual {N} (c : Chart N) (e : ZMod N) : h (c.point e) = h e := by
  cases hc : c.flipped <;> simp [point, hc, parity_residual]

theorem forward_whole_family {N} (c : Chart N) (e : ZMod N) :
    (forward c).physical e = oracle (c.physical e) := by
  cases hc : c.flipped <;>
    simp [physical, forward, point, oracle, Quad.eval_add, Quad.eval_residual, hc, h] <;> ring

theorem reverse_whole_family {N} (c : Chart N) (e : ZMod N) :
    (reverse c).physical e = adjoint (c.physical e) := by
  cases hc : c.flipped <;>
    simp [physical, reverse, point, adjoint, Quad.eval_sub, Quad.eval_residual, hc, h] <;> ring

/-- Coherent amplitude at a physical coordinate, using the inverse chart.
The source interval and its four residue sectors are retained explicitly. -/
def amplitudeAt {N} (c : Chart N) (e r : ZMod N) (coordinate : Nat) : G :=
  let parameter := if c.flipped then 1-e else e
  if 2 ≤ parameter.val ∧ parameter.val < N ∧ parameter.val % 4 = c.sector ∧
      c.residual.eval parameter = r then c.amplitude.get coordinate else 0

end Chart

structure Bank (N : Nat) where
  path : List Nat
  data : List (Chart N)
  deriving DecidableEq, Inhabited

structure Observation (N : Nat) where
  truth : List (Chart N)
  falsity : List (Chart N)
  phaseClass : Nat
  phaseCycle : List (List (Chart N))
  deriving DecidableEq

structure State (N : Nat) where
  sourceWell : BinaryWell
  original : List (Chart N)
  truth : List (Chart N)
  falsity : List (Chart N)
  joint : List (Chart N)
  live : List (Chart N)
  banks : List (Bank N)
  observation : Option (Observation N)
  openFrames : List (List Nat)
  edgeFlags : Array Reg16_3
  nodeInputs : List Nat
  pc : Nat
  fused : Bool
  clears : Nat
  failure : Option String
  deriving DecidableEq

instance (N : Nat) : Repr (State N) where
  reprPrec s _ := "source-split(pc=" ++ repr s.pc ++ ", charts=" ++ repr s.joint.length ++ ", banks=" ++ repr s.banks.length ++ ")"

inductive Op where
  | vinit | tanch | imscrib | fsplit | evalt | afwd | clink | evalf | arev | engagr | ifix | ffuse
  deriving DecidableEq, Repr, Inhabited

structure Wire where
  source : Nat
  port : Bool
  target : Nat
  deriving DecidableEq, Repr, Inhabited

-- GENERATED GRAPH FROM THE USER-SUPPLIED ARTIFACT BELOW
def artifactId : String := "567e94199000485c8a86d2924dc424cc"
def word : String := "⊢⊣⊙∈⊤≻⋈⊥≺⊞⊡∋⋈⊣"
def ops : Array Op := #[.vinit, .tanch, .imscrib, .fsplit, .evalt, .afwd, .clink, .evalf, .arev, .engagr, .ifix, .ffuse, .clink, .tanch]
def wires : Array Wire := #[⟨4, false, 5⟩, ⟨5, false, 6⟩, ⟨3, true, 4⟩, ⟨6, false, 11⟩, ⟨7, false, 8⟩, ⟨8, false, 9⟩, ⟨9, false, 10⟩, ⟨3, false, 7⟩, ⟨10, false, 11⟩, ⟨0, false, 1⟩, ⟨1, false, 2⟩, ⟨2, false, 3⟩, ⟨11, false, 12⟩, ⟨12, false, 13⟩]
def expectedInputs : List Nat := [0, 15, 15, 15, 5, 5, 5, 10, 10, 5, 13, 13, 13, 13]

def mask (x : Reg16_3) : Nat :=
  (if x.bigT then 1 else 0)+(if x.bigF then 2 else 0)+
  (if x.smallT then 4 else 0)+(if x.smallF then 8 else 0)

def flagOut (op : Op) (input : Reg16_3) (truthPort : Bool) : Reg16_3 :=
  match op with
  | .vinit => Imscribing.IUTT.allLanes
  | .fsplit => if truthPort then Imscribing.IUTT.positive input else Imscribing.IUTT.negative input
  | .evalt => Imscribing.IUTT.positive input
  | .evalf => Imscribing.IUTT.negative input
  | .arev => input.invol
  | .engagr => input.engagr
  | _ => input

def prepare (N : Nat) : State N := Id.run do
  let base : Amp := ⟨1,1,1,imaginary⟩
  let charts := (List.range 4).map fun sector =>
    let amp := match sector with
      | 0 => base
      | 1 => base.flip
      | 2 => ⟨base.c,base.d,base.a,base.b⟩
      | _ => ⟨base.d,base.c,base.b,base.a⟩
    ({sector:=sector,flipped:=false,residual:=Quad.zero N,amplitude:=amp,ancestry:=none} : Chart N)
  return ⟨Nat.digits 2 N,charts,[],[],[],charts,[⟨[0],charts⟩],none,[],
    Array.replicate wires.size Imscribing.IUTT.empty,[],0,false,0,none⟩

def bank {N} (s : State N) (path : List Nat) (data : List (Chart N)) : State N :=
  {s with banks := s.banks ++ [⟨path,data⟩]}

def scaleCharts {N} (z : G) (charts : List (Chart N)) : List (Chart N) :=
  charts.map fun c => {c with amplitude:=c.amplitude.scale z}

def phaseUnit (N : Nat) : G := if N % 2 == 0 then 1 else -1

theorem phase_square (N : Nat) : phaseUnit N * phaseUnit N = 1 := by
  unfold phaseUnit; split_ifs <;> simp

theorem phase_involution (N : Nat) (a : Amp) :
    (a.scale (phaseUnit N)).scale (phaseUnit N) = a := by
  cases a
  simp only [Amp.scale]
  congr 1 <;> rw [←mul_assoc, phase_square, one_mul]

def step {N} (s : State N) : State N := Id.run do
  if s.failure.isSome || s.pc >= ops.size then return s
  let node := s.pc
  let op := ops[node]!
  let mut input := Imscribing.IUTT.empty
  for i in [:wires.size] do
    if wires[i]!.target == node then input := input.union s.edgeFlags[i]!
  let mut s := {s with nodeInputs:=s.nodeInputs ++ [mask input]}
  match op with
  | .vinit => s := {s with live:=s.original}
  | .tanch =>
    if node == 1 then s := {s with openFrames:=[[0]]}
    if node+1 == ops.size then
      if !s.fused || s.observation.isNone then
        return {s with failure:=some "terminal return preceded fixation or fuse"}
      if s.openFrames != [[0]] then return {s with failure:=some "outer frame did not return"}
      s := bank {s with openFrames:=[]} [0,13] s.joint
  | .imscrib =>
    if binEval s.sourceWell != N then return {s with failure:=some "source bank changed"}
  | .fsplit =>
    if s.openFrames != [[0]] then return {s with failure:=some "split has no containing frame"}
    s := {s with openFrames:=[0,3]::s.openFrames}
    let truth := s.original.map fun c => {c with amplitude:=c.amplitude.truth,ancestry:=some false}
    let falsity := s.original.map fun c => {c with amplitude:=c.amplitude.falsity,ancestry:=some true}
    s := bank {s with truth:=truth,falsity:=falsity,live:=truth++falsity} [0,3] (truth++falsity)
  | .evalt => s := {s with live:=s.truth}
  | .afwd =>
    let changed := s.truth.map Chart.forward
    s := bank {s with truth:=changed,live:=changed} [0,3,5] changed
  | .clink =>
    if s.fused then
      let changed := s.joint.map fun c => {c with amplitude:=c.amplitude.clink}
      s := bank {s with joint:=changed,live:=changed} [0,12] changed
    else
      let changed := s.truth.map fun c => {c with amplitude:=c.amplitude.clink}
      s := bank {s with truth:=changed,live:=changed} [0,3,6] changed
  | .evalf => s := {s with live:=s.falsity}
  | .arev =>
    if s.openFrames.head? != some [0,3] then return {s with failure:=some "clear has no working frame"}
    -- Deposit inside the open working frame, clear the live register, and
    -- retrieve that very deposit before applying the adjoint and parity.
    s := bank s [0,3,8] s.falsity
    s := {s with live:=[],falsity:=[],clears:=s.clears+1}
    let restored := (s.banks.getLast!).data
    let changed := restored.map fun c => Chart.parity (Chart.reverse c)
    s := {s with falsity:=changed,live:=changed}
  | .engagr => s := bank {s with live:=s.truth++s.falsity} [0,3,9] (s.truth++s.falsity)
  | .ifix =>
    let before := s.falsity
    let measured := scaleCharts (phaseUnit N) before
    let returned := scaleCharts (phaseUnit N) measured
    if returned != before then return {s with failure:=some "Z2 phase cycle failed"}
    let observation := Observation.mk s.truth measured (N%2) [before,measured,returned]
    s := bank {s with falsity:=measured,live:=measured,observation:=some observation} [0,3,10] measured
  | .ffuse =>
    if s.openFrames.head? != some [0,3] || s.observation.isNone then
      return {s with failure:=some "fuse lost its frame or fixed observation"}
    s := {s with openFrames:=s.openFrames.tail}
    let joined := (s.truth++s.falsity).map fun c => {c with ancestry:=none}
    s := bank {s with joint:=joined,live:=joined,fused:=true} [0,11] joined
  let mut edges := s.edgeFlags
  for i in [:wires.size] do
    if wires[i]!.source == node then edges := edges.set! i (flagOut op input wires[i]!.port)
  return {s with edgeFlags:=edges,pc:=node+1}

/-- Untagged return: amplitudes add coherently across overlapping chart images. -/
def amplitudeAt {N} (charts : List (Chart N)) (e r : ZMod N) (coordinate : Nat) : G :=
  charts.foldl (fun total c => total+c.amplitudeAt e r coordinate) 0

end Imscribing.Paraconsistent.SourceBoundSplit
