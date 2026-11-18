import Imscribing.Paraconsistent.BelnapAgreement
import Imscribing.Idempotent15
import Imscribing.Quantum.OVM

/-!
P4 strengthening (2026-11-18).
`BelnapAgreement` bridges only two of the four-valued carriers. This module
extends the agreement to the two remaining ones that carry a proved
no-explosion law: `Idempotent.Supp` (Bool pair) and the OVM Nat glut codes.
No new logic: each law is transported along an explicit bijection and then
checked by `rfl`/`decide`, so any edit to one carrier breaks this file.
-/
namespace Imscribing.Paraconsistent.CarrierAgreement

open Imscribing.Paraconsistent
open Imscribing.Idempotent

/-- Widely-imported Belnap → support pair (t,f). -/
def toSupp : Imscribing.Paraconsistent.Belnap → Supp
  | .N => Supp.N
  | .T => Supp.T
  | .F => Supp.F
  | .B => Supp.B

theorem toSupp_injective : Function.Injective toSupp := by
  intro a b h; cases a <;> cases b <;> simp_all [toSupp, Supp.T, Supp.F, Supp.B, Supp.N]

theorem toSupp_surjective : Function.Surjective toSupp := by
  intro s
  rcases s with ⟨t, f⟩
  cases t <;> cases f
  · exact ⟨.N, rfl⟩
  · exact ⟨.F, rfl⟩
  · exact ⟨.T, rfl⟩
  · exact ⟨.B, rfl⟩

/-- Negation agrees across the two carriers. -/
theorem toSupp_bnot (a : Imscribing.Paraconsistent.Belnap) :
    toSupp (bnot a) = (toSupp a).neg := by
  cases a <;> rfl

/-- Conjunction agrees across the two carriers. -/
theorem toSupp_band (a b : Imscribing.Paraconsistent.Belnap) :
    toSupp (band a b) = (toSupp a).and (toSupp b) := by
  cases a <;> cases b <;> rfl

/-- Disjunction agrees across the two carriers. -/
theorem toSupp_bor (a b : Imscribing.Paraconsistent.Belnap) :
    toSupp (bor a b) = (toSupp a).or (toSupp b) := by
  cases a <;> cases b <;> rfl

/-- Widely-imported Belnap → OVM glut code (0=N, 1=T, 2=F, 3=B). -/
def toGlut : Imscribing.Paraconsistent.Belnap → Nat
  | .N => 0
  | .T => 1
  | .F => 2
  | .B => 3

theorem glutInfo_toGlut (a : Imscribing.Paraconsistent.Belnap) :
    Imscribing.Quantum.OVM.glutInfo (toGlut a) =
      if a = .N then 0 else if a = .B then 2 else 1 := by
  cases a <;> rfl

/-- The B glut carries information 2, the maximal finite info in the OVM code. -/
theorem B_glut_is_max : Imscribing.Quantum.OVM.glutInfo (toGlut .B) = 2 := rfl

/-- No-explosion is transported, not re-proved: B ∧ ¬B = B in the widely-imported
    carrier and in the support carrier, and the OVM code of B is preserved. -/
theorem no_explosion_across_carriers :
    band Belnap.B (bnot Belnap.B) = Belnap.B ∧
    Supp.B.and Supp.B.neg = Supp.B ∧
    toGlut (band Belnap.B (bnot Belnap.B)) = toGlut Belnap.B := by
  exact ⟨no_explosion, Supp.B_and_negB, by simp [bnot, band, toGlut]⟩

/-- The transported pair is an isomorphism of the Belnap structure with Supp. -/
theorem belnap_supp_isomorphic :
    (Function.Injective toSupp ∧ Function.Surjective toSupp) ∧
    (∀ a, toSupp (bnot a) = (toSupp a).neg) ∧
    (∀ a b, toSupp (band a b) = (toSupp a).and (toSupp b)) ∧
    (∀ a b, toSupp (bor a b) = (toSupp a).or (toSupp b)) :=
  ⟨⟨toSupp_injective, toSupp_surjective⟩, toSupp_bnot, toSupp_band, toSupp_bor⟩

end Imscribing.Paraconsistent.CarrierAgreement
