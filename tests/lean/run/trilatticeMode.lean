import Init.Paraconsistent

open Lean

inductive EmptyParameter (n : Nat) : Prop
inductive EmptyIndex : Nat → Prop

-- Check the native kernel with the same raw False recursor in all four flag states.
run_elab do
  let base ← Lean.getEnv
  let base := base.unmarkParaconsistent.unmarkTrilattice
  for para in [false, true] do
    for tri in [false, true] do
      let env := (if para then base.markParaconsistent else base)
      let env := if tri then env.markTrilattice else env
      unless env.isParaconsistent == para && env.isTrilattice == tri &&
          env.holdsContradictions == (para || tri) do
        throwError "kernel mode flag mismatch"
      let type ← mkArrow (mkConst ``False) (mkConst ``Nat)
      let value := mkLambda `h .default (mkConst ``False)
        (mkApp2 (mkConst ``False.rec [Level.succ Level.zero])
          (mkLambda `x .default (mkConst ``False) (mkConst ``Nat)) (mkBVar 0))
      let decl := Declaration.defnDecl {
        name := `rawExplosionControl, levelParams := [], type, value,
        hints := .regular 0, safety := .safe }
      match env.addDeclCore 0 decl none (doCheck := true) with
      | .ok _ => if para || tri then throwError "native kernel admitted explosion in contradiction mode"
      | .error _ => unless para || tri do throwError "classical control rejected raw explosion"
      let predicate := mkApp (mkConst ``EmptyParameter) (mkNatLit 0)
      let parameterType ← mkArrow predicate (mkConst ``Nat)
      let parameterDecl := Declaration.defnDecl {
        name := `parameterExplosionControl, levelParams := [],
        type := parameterType,
        value := mkLambda `h .default predicate
          (mkApp3 (mkConst ``EmptyParameter.rec [Level.succ Level.zero])
            (mkNatLit 0) (mkLambda `x .default predicate (mkConst ``Nat)) (mkBVar 0)),
        hints := .regular 0, safety := .safe }
      match env.addDeclCore 0 parameterDecl none (doCheck := true) with
      | .ok _ => if para || tri then throwError "native kernel admitted parameterized Prop explosion"
      | .error err => unless para || tri do throwKernelException err
      let emptyType ← mkArrow (mkConst ``Empty) (mkConst ``Nat)
      let typeDecl := Declaration.defnDecl {
        name := `emptyTypeControl, levelParams := [],
        type := emptyType,
        value := mkLambda `h .default (mkConst ``Empty)
          (mkApp2 (mkConst ``Empty.rec [Level.succ Level.zero])
            (mkLambda `x .default (mkConst ``Empty) (mkConst ``Nat)) (mkBVar 0)),
        hints := .regular 0, safety := .safe }
      match env.addDeclCore 0 typeDecl none (doCheck := true) with
      | .ok _ => pure ()
      | .error _ => throwError "native kernel rejected empty Type elimination"
      for predicateName in [``False, ``EmptyParameter, ``EmptyIndex] do
        match mkCasesOnImp env.toKernelEnv predicateName with
        | .ok _ => if para || tri then throwError "native kernel generated empty Prop casesOn"
        | .error err => unless para || tri do throwKernelException err
      match mkCasesOnImp env.toKernelEnv ``Empty with
      | .ok _ => pure ()
      | .error err => throwKernelException err
      unless !env.unmarkTrilattice.isTrilattice &&
          env.unmarkTrilattice.holdsContradictions == para &&
          !env.unmarkParaconsistent.isParaconsistent &&
          env.unmarkParaconsistent.holdsContradictions == tri do
        throwError "kernel mode disable round trip failed"

/-- error: re-entry declarations require paraconsistent or SIXTEEN_3 mode -/
#guard_msgs in
reentry modeOff (f : Sixteen3) : Sixteen3 := f

enable_trilattice

/-- error: re-entry must bind exactly one parameter of type `Lean.Sixteen3` -/
#guard_msgs in
reentry extraBinder (f g : Sixteen3) : Sixteen3 := Sixteen3.join_i f g

/-- error: the re-entry parameter must have type `Lean.Sixteen3` -/
#guard_msgs in
reentry wrongBinder (f : Nat) : Sixteen3 := Sixteen3.none

/-- error: a re-entry declaration must have type `Lean.Sixteen3` -/
#guard_msgs in
reentry wrongResult (f : Sixteen3) : Nat := 0

/-- error: the body must depend on its re-entry parameter -/
#guard_msgs in
reentry constantBody (f : Sixteen3) : Sixteen3 := Sixteen3.all

/-- error: the re-entry map must be monotone in the information order -/
#guard_msgs in
reentry nonmonotone (f : Sixteen3) : Sixteen3 :=
  ⟨!f.hasN, !f.hasT, !f.hasF, !f.hasB⟩

namespace NamedControl
private reentry privateValue (f : Sixteen3) : Sixteen3 := Sixteen3.join_i f Sixteen3.all
example : privateValue = Sixteen3.all := rfl
#eval show IO Unit from do
  unless privateValue == Sixteen3.all do throw <| IO.userError "private runtime payload"
end NamedControl

section
variable (unused : Nat)
reentry sectionValue (f : Sixteen3) : Sixteen3 := Sixteen3.join_i f Sixteen3.all
example : sectionValue = Sixteen3.all := rfl
end

reentry QualifiedControl.value (f : Sixteen3) : Sixteen3 := Sixteen3.join_i f Sixteen3.all
example : QualifiedControl.value = Sixteen3.all := rfl

-- Four strict ascents require the complete height bound before stability.
reentry propagation (f : Sixteen3) : Sixteen3 := ⟨true, f.hasN, f.hasT, f.hasF⟩
example : propagation = Sixteen3.all := rfl
#eval show IO Unit from do
  unless propagation == Sixteen3.all do throw <| IO.userError "propagation fixed point"
