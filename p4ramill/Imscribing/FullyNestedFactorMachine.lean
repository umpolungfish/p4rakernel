namespace Imscribing.FullyNestedFactorMachine

/-! The executable path is deliberately unboxed. Every definition below
compiles to scalar native control flow that `vox` lifts into the twelve marks;
there is no call from the lifted machine into Lean's allocation runtime. -/

@[noinline] def afwd (a : UInt64) : UInt64 := a + 1
@[noinline] def evalt (a n : UInt64) : UInt64 := a * a - n

@[noinline] def squareLe (x n : UInt64) : Bool := x == 0 || x ≤ n / x

partial def arev (n x : UInt64) : UInt64 :=
  let y := afwd x
  if y > x && squareLe y n then arev n y else x

@[noinline] def evalf (b delta : UInt64) : Bool := b * b == delta
@[noinline] def clinkP (a b : UInt64) : UInt64 := a - b
@[noinline] def clinkQ (a b : UInt64) : UInt64 := a + b
@[noinline] def imscrib (p q n : UInt64) : Bool := p > 1 && p * q == n
@[noinline] def ifix (square valid : Bool) : Bool := square && valid
@[noinline] def tanch (fixed : Bool) (p : UInt64) : UInt64 := if fixed then p else 0

partial def phase (n a fuel : UInt64) : UInt64 :=
  if fuel == 0 then 0
  else
    let nextA := afwd a
    let delta := evalt nextA n
    let b := arev delta 0
    let square := evalf b delta
    let p := clinkP nextA b
    let q := clinkQ nextA b
    let valid := imscrib p q n
    let emitted := tanch (ifix square valid) p
    if emitted == 0 then phase n nextA (fuel - 1) else emitted

@[export nested_factor_u64]
def nestedFactorU64 (n start fuel : UInt64) : UInt64 := phase n (start - 1) fuel

end Imscribing.FullyNestedFactorMachine
