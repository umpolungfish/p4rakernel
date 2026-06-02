import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Algebra
open Imscribing.Primitives

#check compute_meet
#check scalarField_Kslow

-- Test: meet(a, a) = a
example (a : Imscription) : compute_meet a a = a := by
  unfold compute_meet
  ext <;> simp

-- Test: tensorProduct(a, a) = a
example (a : Imscription) : tensorProduct a a = a := by
  unfold tensorProduct
  ext <;> simp

-- Test: join(bottom, a) = a
def frobenius_bottom : Imscription := {
  dim := D_wedge, top := T_network, rel := R_super, pol := P_asym,
  fid := F_ell, kin := K_fast, gran := G_beth, gram := Gamma_and,
  crit := Phi_sub, chir := H0, stoi := one_one, prot := Omega_0
}
example (a : Imscription) : compute_join frobenius_bottom a = a := by
  unfold compute_join frobenius_bottom
  ext <;> simp
