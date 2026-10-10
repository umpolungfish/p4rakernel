import Imscribing.NS_KernelReentry
import Mathlib.Lean.Expr.Basic

open Lean Imscribing.NSReentry

-- Imported native values reduce inside proofs and preserve declaration metadata.
example : nativeHeld.hasB = true := rfl
example : nativeHeld.hasN = false := rfl
example : nativeHeld.hasT = false := rfl
example : nativeHeld.hasF = false := rfl

run_elab do
  let info ← Lean.getConstInfo ``nativeHeld
  let renamed := info.updateName `nsHeldMetadataControl
  unless renamed.name == `nsHeldMetadataControl do
    throwError "native metadata update failed"
  match renamed.toDeclaration! with
  | .reentryDecl value =>
    unless value.six3 == Sixteen3.ofBelnap false false false true do
      throwError "native payload conversion failed"
  | _ => throwError "native declaration kind lost"

#eval show IO Unit from do
  for mask in [:16] do
    let state := Sixteen3.ofMask mask
    let upper : RegisteredScale Nat 2 := ((((), false), false), 37, state)
    let returned := registeredReEntry upper
    unless returned.2.1 == 37 do
      throw <| IO.userError "field content changed"
    unless returned.2.2 == heldClosure state do
      throw <| IO.userError "register normalization mismatch"
    unless (registeredCollapse (registeredCollapse upper)).2.2 ==
        (registeredCollapse upper).2.2 do
      throw <| IO.userError "feedback failed to stabilize"
    unless returned.2.2.hasN == state.hasN && returned.2.2.hasT == state.hasT &&
        returned.2.2.hasF == state.hasF && returned.2.2.hasB do
      throw <| IO.userError "membership preservation failed"
  IO.println "Imported native NS feedback: all registers preserve the field and stabilize."

#print axioms heldClosure_least
#print axioms registeredCollapse_idempotent
#print axioms registered_round_trip_fixed
#print axioms Imscribing.NSInjectionField.registered_injection_connection
#print axioms Imscribing.NSInjectionField.registered_injection_smooth
