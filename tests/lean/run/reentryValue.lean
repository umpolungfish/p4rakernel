import Lean

open Lean

-- Exercise every membership mask and its declaration metadata/expression payload.
#eval show IO Unit from do
  let mut env ← mkEmptyEnvironment
  for mask in [0:16] do
    let bit (n : Nat) : Bool := mask / (2 ^ n) % 2 == 1
    let v : Sixteen3 := ⟨bit 0, bit 1, bit 2, bit 3⟩
    let val : ReentryVal := {
      name := `reentryControl
      levelParams := []
      type := mkConst ``Sixteen3
      six3 := v }
    let info := ConstantInfo.reentryInfo val
    let boolExpr (b : Bool) := mkConst (if b then ``Bool.true else ``Bool.false)
    let expected := mkApp4 (mkConst ``Sixteen3.mk) (boolExpr v.hasN)
      (boolExpr v.hasT) (boolExpr v.hasF) (boolExpr v.hasB)
    unless info.type == mkConst ``Sixteen3 && info.value? == some expected &&
        info.value! == expected && info.hasValue && !info.isUnsafe && !info.isPartial do
      throw <| IO.userError s!"reentry payload mismatch at mask {mask}"
    -- This control isolates the native storage ABI without type checking.
    let storedVal := { val with name := Name.num `reentryControl mask }
    match env.addDeclCore 0 (.reentryDecl storedVal) none (doCheck := false) with
    | .error _ => throw <| IO.userError s!"native reentry insertion failed at mask {mask}"
    | .ok next => env := next
    let some stored := env.find? storedVal.name
      | throw <| IO.userError s!"native reentry disappeared at mask {mask}"
    unless stored.type == storedVal.type && stored.value? == some expected do
      throw <| IO.userError s!"native reentry round-trip mismatch at mask {mask}"

-- The real native kernel checks each payload, and rejects a mismatched declared type.
run_elab do
  let mut env ← Lean.getEnv
  for mask in [0:16] do
    let bit (n : Nat) : Bool := mask / (2 ^ n) % 2 == 1
    let val : ReentryVal := {
      name := Name.num `checkedReentryControl mask
      levelParams := []
      type := mkConst ``Sixteen3
      six3 := ⟨bit 0, bit 1, bit 2, bit 3⟩ }
    match env.addDeclCore 0 (.reentryDecl val) none (doCheck := true) with
    | .error _ => throwError "checked native insertion failed at mask {mask}"
    | .ok next => env := next
    let bad := { val with name := Name.num `invalidReentryControl mask, type := mkConst ``Nat }
    match env.addDeclCore 0 (.reentryDecl bad) none (doCheck := true) with
    | .error _ => pure ()
    | .ok _ => throwError "native kernel accepted a SIXTEEN_3 payload as Nat"
