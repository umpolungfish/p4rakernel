import Mathlib

namespace Imscribing.Paraconsistent.CongruenceSelection

/-- Modular powering without constructing the unreduced power. -/
def power (a exponent modulus : Nat) : Nat := Id.run do
  let mut a := a % modulus
  let mut e := exponent
  let mut r := 1
  while e > 0 do
    if e % 2 == 1 then r := r*a % modulus
    a := a*a % modulus
    e := e/2
  return r

/-- Tonelli-Shanks on an odd prime. The returned root is checked by its caller. -/
def root (n p : Nat) : Option Nat := Id.run do
  if p == 2 then return some (n%2)
  if n%p == 0 then return some 0
  if power n ((p-1)/2) p != 1 then return none
  let mut q := p-1
  let mut s := 0
  while q%2 == 0 do
    q := q/2
    s := s+1
  let mut z := 2
  while z < p && power z ((p-1)/2) p != p-1 do z := z+1
  if z == p then return none
  let mut c := power z q p
  let mut x := power n ((q+1)/2) p
  let mut t := power n q p
  let mut m := s
  while t != 1 do
    let mut i := 0
    let mut v := t
    while v != 1 && i < m do
      v := v*v%p
      i := i+1
    if i == m then return none
    let b := power c (2^(m-i-1)) p
    x := x*b%p
    t := t*b*b%p
    c := b*b%p
    m := i
  return some x

structure PrimeRoot where
  prime : Nat
  residue : Nat
  deriving Inhabited, DecidableEq, Repr

def factorBase (N bound : Nat) : Array PrimeRoot := Id.run do
  let mut sieve := Array.replicate (bound+1) true
  let mut base := #[]
  for p in [2:bound+1] do
    if sieve[p]! then
      let mut multiple := p*p
      while multiple ≤ bound do
        sieve := sieve.set! multiple false
        multiple := multiple+p
      if let some r := root N p then
        if r*r%p == N%p then base := base.push ⟨p,r⟩
  return base

/-- X² = Y² times the odd factor-base product, modulo the retained N. -/
structure Relation where
  x : Nat := 1
  y : Nat := 1
  parity : Nat := 0
  deriving Inhabited, DecidableEq, Repr

def combine (N : Nat) (base : Array PrimeRoot) (a b : Relation) : Relation := Id.run do
  let mut y := a.y*b.y%N
  let common := Nat.land a.parity b.parity
  for i in [:base.size] do
    if common.testBit i then y := y*base[i]!.prime%N
  return ⟨a.x*b.x%N,y,Nat.xor a.parity b.parity⟩

structure Cell extends Relation where
  remaining : Nat := 1
  deriving Inhabited, DecidableEq, Repr

structure State where
  base : Array PrimeRoot := #[]
  pivots : Array (Option Relation) := #[]
  cells : Array Cell := #[]
  nextX : Nat := 0
  primeIndex : Nat := 0
  positions : Nat := 0
  relations : Nat := 0
  dependencies : Nat := 0
  eliminations : Nat := 0
  partials : Array (List (Nat × Relation)) := #[]
  paired : Nat := 0
  divisor : Option Nat := none
  witness : Option (Nat × Nat) := none
  failure : Option String := none
  deriving Inhabited, DecidableEq, Repr

def prepare (N : Nat) (bound : Nat := 30000) : State :=
  let base := factorBase N bound
  {base:=base,pivots:=Array.replicate base.size none,nextX:=Nat.sqrt N+1,
   partials:=Array.replicate 65536 []}

def proper (N d : Nat) : Bool := 1 < d && d < N && N%d == 0

def insert (N : Nat) (s : State) (input : Relation) : State := Id.run do
  let mut s := {s with relations:=s.relations+1}
  let mut row := input
  for offset in [:s.base.size] do
    let bit := s.base.size-1-offset
    if row.parity.testBit bit then
      if let some pivot := s.pivots[bit]! then
        row := combine N s.base row pivot
        s := {s with eliminations:=s.eliminations+1}
      else
        return {s with pivots:=s.pivots.set! bit (some row)}
  if row.x*row.x%N != row.y*row.y%N then
    return {s with failure:=some "relation dependency lost its square congruence"}
  s := {s with dependencies:=s.dependencies+1}
  let d := Nat.gcd (row.x+N-row.y) N
  let other := Nat.gcd (row.x+row.y) N
  if proper N d then return {s with divisor:=some d,witness:=some (row.x,row.y)}
  if proper N other then return {s with divisor:=some other,witness:=some (row.x,row.y)}
  return s

/-- One retained sieve operation. A Y return preserves the partially sieved
block and every independent relation. The base primes divide polynomial
values, rather than serving as successive candidate divisors of N. -/
def step (N : Nat) (s : State) : State := Id.run do
  if s.divisor.isSome || s.failure.isSome then return s
  let mut s := s
  if s.cells.isEmpty then
    let mut cells := #[]
    for i in [:8192] do
      let x := s.nextX+i
      cells := cells.push {x:=x%N,remaining:=x*x-N : Cell}
    s := {s with cells:=cells,primeIndex:=0,nextX:=s.nextX+8192}
  while s.primeIndex < s.base.size do
    let entry := s.base[s.primeIndex]!
    let p := entry.prime
    let startX := s.nextX-s.cells.size
    let mut cells := s.cells
    s := {s with cells:=#[]}
    for r in ([entry.residue,(p-entry.residue)%p].eraseDups) do
      let mut index := (r+p-startX%p)%p
      while index < cells.size do
        let mut cell := cells[index]!
        let mut exponent := 0
        while cell.remaining > 1 && cell.remaining%p == 0 do
          cell := {cell with remaining:=cell.remaining/p}
          exponent := exponent+1
        if exponent%2 == 1 then
          cell := {cell with parity:=Nat.xor cell.parity (2^s.primeIndex)}
        if exponent ≥ 2 then
          cell := {cell with y:=cell.y * power p (exponent/2) N % N}
        cells := cells.set! index cell
        index := index+p
    s := {s with cells:=cells,primeIndex:=s.primeIndex+1}
  for cell in s.cells do
    if cell.remaining == 1 then
      s := insert N s cell.toRelation
      if s.divisor.isSome || s.failure.isSome then break
    else if cell.remaining > 1 && cell.remaining ≤ 900000000 then
      let square := Nat.sqrt cell.remaining
      if square*square == cell.remaining then
        s := insert N s {cell.toRelation with y:=cell.y*square%N}
      else
        let bucket := cell.remaining%s.partials.size
        let entries := s.partials[bucket]!
        if let some (_,previous) := entries.find? (fun pair => pair.1 == cell.remaining) then
          let joined := combine N s.base cell.toRelation previous
          s := insert N {s with paired:=s.paired+1}
            {joined with y:=joined.y*cell.remaining%N}
          s := {s with partials:=s.partials.set! bucket (entries.filter fun pair => pair.1 != cell.remaining)}
        else
          s := {s with partials:=s.partials.set! bucket ((cell.remaining,cell.toRelation)::entries)}
      if s.divisor.isSome || s.failure.isSome then break
  return {s with cells:=#[],positions:=s.positions+s.cells.size}

end Imscribing.Paraconsistent.CongruenceSelection
