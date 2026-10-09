import Imscribing.Paraconsistent.SixteenThreeTrilattice
import Imscribing.Paraconsistent.FrobeniusFiltration

open Imscribing.Paraconsistent.SixteenThreeTrilattice

namespace Reg16_3_check
open Reg16_3

#check @invol_eq_compose
#check @leqI_refl
#check @leqI_union_left
#check @union_least_upper_bound
#check @engagr_holds_both

#print axioms invol_eq_compose
#print axioms leqI_union_left
#print axioms union_least_upper_bound
#print axioms engagr_holds_both
#print axioms sixteen_three_verified
end Reg16_3_check
