import Imscribing.Paraconsistent.PrimaLogicaFragments

/-!
# Prima Logica audit

Build separately after placing the three files into p4ramill/Imscribing/Paraconsistent/.
No new axiom, sorry, or custom kernel primitive is introduced by these files.
-/

open Lean Imscribing.PrimaLogica

#check L5_LP_inclosure_four_from_any
#check lpInclosure_unmarked
#check L5_LP_terminal_is_unifiedB
#check wind_four_from_any
#check wind_monotone
#check wind_fixed_iff_complete
#check unifiedB_join_left
#check unifiedB_join_right
#check winding_commutes_with_native_closure
#check winding_eq_native_closure_iff
#check winding_agrees_with_native_closure_at_stage_three
#check winding_differs_from_B_closure_at_unmarked
#check gapIntoFour_injective
#check glutIntoFour_injective
#check every_singleton_below_complete

#print axioms wind_four_from_any
#print axioms wind_monotone
#print axioms wind_fixed_iff_complete
#print axioms gapIntoFour_injective

#eval show IO Unit from do
  for mask in [:16] do
    let s := Sixteen3.ofMask mask
    let step4 := wind (wind (wind (wind s)))
    unless step4 == complete do
      throw <| IO.userError "winding failed to reach full Inclosure"
    unless Sixteen3.le_i s (wind s) == true do
      throw <| IO.userError "winding lost information"
  IO.println "Prima Logica winding: all 16 starting states reach the full register."
