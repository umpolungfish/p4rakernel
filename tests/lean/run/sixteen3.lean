import Init.Paraconsistent

open Lean

def valueOfMask (m : Nat) : Sixteen3 :=
  ⟨m % 2 == 1, m / 2 % 2 == 1, m / 4 % 2 == 1, m / 8 % 2 == 1⟩

-- Regression: empty and {N} must remain distinct in every partial order.
example : Sixteen3.le_t Sixteen3.none (valueOfMask 1) = false := rfl
example : Sixteen3.le_f Sixteen3.none (valueOfMask 1) = false := rfl
example : Sixteen3.join_t (valueOfMask 2) (valueOfMask 8) = valueOfMask 10 := rfl
example : Sixteen3.join_f (valueOfMask 4) (valueOfMask 8) = valueOfMask 12 := rfl

#eval show IO Unit from do
  let values := (List.range 16).map valueOfMask
  let orders := [(Sixteen3.le_i, Sixteen3.join_i, Sixteen3.meet_i, 0),
    (Sixteen3.le_t, Sixteen3.join_t, Sixteen3.meet_t, 5),
    (Sixteen3.le_f, Sixteen3.join_f, Sixteen3.meet_f, 3)]
  for (le, join, meet, reversed) in orders do
    for m in [0:16] do
      let x := valueOfMask m
      unless le x x do throw <| IO.userError "reflexivity"
      for n in [0:16] do
        let y := valueOfMask n
        -- Independent oracle: each order is subset inclusion after reversing its negative bits.
        let mx := m ^^^ reversed
        let ny := n ^^^ reversed
        unless le x y == ((mx &&& ny) == mx) do
          throw <| IO.userError s!"order mismatch: {reversed}, {m}, {n}"
        unless join x y == valueOfMask ((mx ||| ny) ^^^ reversed) &&
            meet x y == valueOfMask ((mx &&& ny) ^^^ reversed) do
          throw <| IO.userError "lattice operation mismatch"
        if le x y && le y x && x != y then throw <| IO.userError "antisymmetry"
        unless le x (join x y) && le y (join x y) &&
            le (meet x y) x && le (meet x y) y do
          throw <| IO.userError "bounds"
        unless join x y == join y x && meet x y == meet y x &&
            meet x (join x y) == x && join x (meet x y) == x do
          throw <| IO.userError "commutativity or absorption"
        for z in values do
          if le x y && le y z && !le x z then throw <| IO.userError "transitivity"
          if le x z && le y z && !le (join x y) z then throw <| IO.userError "least upper bound"
          if le z x && le z y && !le z (meet x y) then throw <| IO.userError "greatest lower bound"
          unless join (join x y) z == join x (join y z) &&
              meet (meet x y) z == meet x (meet y z) &&
              meet x (join y z) == join (meet x y) (meet x z) do
            throw <| IO.userError "associativity or distributivity"
          -- Every lattice operation is monotone in each of the three orders.
          for (otherLe, _, _, _) in orders do
            if otherLe x y && (!(otherLe (join x z) (join y z)) ||
                !(otherLe (meet x z) (meet y z))) then
              throw <| IO.userError "interlacing"

#eval show IO Unit from do
  let values := (List.range 16).toArray.map Sixteen3.ofMask
  unless (Sixteen3.fixedPoint #[]).isNone do
    throw <| IO.userError "malformed table accepted"
  for seed in values do
    unless Sixteen3.fixedPoint (values.map (Sixteen3.join_i · seed)) == some seed &&
        Sixteen3.fixedPoint (values.map (Sixteen3.meet_i · seed)) == some Sixteen3.none do
      throw <| IO.userError "native fixed-point ABI mismatch"
  let complement := values.map fun x => Sixteen3.mk (!x.hasN) (!x.hasT) (!x.hasF) (!x.hasB)
  unless (Sixteen3.fixedPoint complement).isNone do
    throw <| IO.userError "nonmonotone native table accepted"
  -- This map is stable at bottom but violates monotonicity away from the iteration path.
  unless (Sixteen3.fixedPoint (values.set! 15 Sixteen3.none)).isNone do
    throw <| IO.userError "off-path nonmonotone map accepted"
