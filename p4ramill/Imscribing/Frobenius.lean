-- Imscribing/Frobenius.lean
-- Concrete μ and δ operations on the Imscription 12-tuple.
-- Proves μ ∘ δ = id at the tuple level — the Frobenius condition in its
-- special (O_inf) form.  Three independent Frobenius structures:
--
--   §1–§3  Tensor-diagonal Frobenius: δ(a)=(a,a), μ(x,y)=tensorProduct(x,y)
--   §4     Meet-diagonal Frobenius:   δ(a)=(a,a), μ(x,y)=compute_meet(x,y)
--   §5     Lattice-interval:          δ(a)=(⊥,a), μ(x,y)=compute_join(x,y)
--   §6     Polarization Frobenius:    δ splits P/Φ, μ fuses at P_pm_sym/Φ_c
--
-- Reference: PRIMITIVE_THEOREMS §23, PRIMITIVE_PREDICTIONS P-169–P-173.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Algebra

namespace Imscribing.Frobenius

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar Fidelity KineticChar
     Granularity Criticality Protection Stoichiometry Chirality

-- ============================================================
-- §1  Frobenius lattice extremals
-- ============================================================

/-- Bottom element: all 12 primitives at minimum ordinal values. -/
def frobenius_bottom : Imscription := {
  dim  := D_wedge
  top  := T_network
  rel  := R_super
  pol  := P_asym
  fid  := F_ell
  kin  := K_fast
  gran := G_beth
  gram := Gamma_and
  crit := Phi_sub
  chir := H0
  stoi := one_one
  prot := Omega_0
}

/-- Top element: all 12 primitives at maximum ordinal values. -/
def frobenius_top : Imscription := {
  dim  := D_odot
  top  := T_odot
  rel  := R_lr
  pol  := P_pm_sym
  fid  := F_hbar
  kin  := K_trap
  gran := G_aleph
  gram := Gamma_broad
  crit := Phi_super
  chir := H_inf
  stoi := n_m
  prot := Omega_NA
}

-- ============================================================
-- §2  Helper lemmas: each primitive type's minimum is its
--     bottom under the compare ordering.
-- ============================================================

lemma D_bottom_eq (d : Dimensionality) (h : compare D_wedge d ≠ .lt) : D_wedge = d := by
  cases d <;> first | rfl | exfalso; apply h; decide

lemma T_bottom_eq (t : Topology) (h : compare T_network t ≠ .lt) : T_network = t := by
  cases t <;> first | rfl | exfalso; apply h; decide

lemma R_bottom_eq (r : Relational) (h : compare R_super r ≠ .lt) : R_super = r := by
  cases r <;> first | rfl | exfalso; apply h; decide

lemma P_bottom_eq (p : Polarity) (h : compare P_asym p ≠ .lt) : P_asym = p := by
  cases p <;> first | rfl | exfalso; apply h; decide

lemma F_bottom_eq (f : Fidelity) (h : compare F_ell f ≠ .lt) : F_ell = f := by
  cases f <;> first | rfl | exfalso; apply h; decide

lemma K_bottom_eq (k : KineticChar) (h : compare K_fast k ≠ .lt) : K_fast = k := by
  cases k <;> first | rfl | exfalso; apply h; decide

lemma G_bottom_eq (g : Granularity) (h : compare G_beth g ≠ .lt) : G_beth = g := by
  cases g <;> first | rfl | exfalso; apply h; decide

lemma Γ_bottom_eq (g : Grammar) (h : compare Gamma_and g ≠ .lt) : Gamma_and = g := by
  cases g <;> first | rfl | exfalso; apply h; decide

lemma Φ_bottom_eq (c : Criticality) (h : compare Phi_sub c ≠ .lt) : Phi_sub = c := by
  cases c <;> first | rfl | exfalso; apply h; decide

lemma H_bottom_eq (h' : Chirality) (h : compare H0 h' ≠ .lt) : H0 = h' := by
  cases h' <;> first | rfl | exfalso; apply h; decide

lemma S_bottom_eq (s : Stoichiometry) (h : compare one_one s ≠ .lt) : one_one = s := by
  cases s <;> first | rfl | exfalso; apply h; decide

lemma Ω_bottom_eq (o : Protection) (h : compare Omega_0 o ≠ .lt) : Omega_0 = o := by
  cases o <;> first | rfl | exfalso; apply h; decide

-- ============================================================
-- §3  Tensor-diagonal Frobenius (Structure A)
--     δ_A(a) = (a, a)            — diagonal comultiplication
--     μ_A(x, y) = tensorProduct   — structural composition
--     Theorem: μ_A ∘ δ_A = id
-- ============================================================

/-- Diagonal comultiplication: δ_A(a) = (a, a). -/
def δ_A (a : Imscription) : Imscription × Imscription := (a, a)

/-- Tensor multiplication: μ_A(x, y) = tensorProduct(x, y).
    Union primitives (D,T,R,G,Γ,Φ,H,S,Ω) take max; bottlenecks (P,F) take min. -/
def μ_A (x y : Imscription) : Imscription := tensorProduct x y

/-- μ_A ∘ δ_A = id : tensorProduct(a, a) = a for every Imscription a. -/
theorem mu_delta_A_id (a : Imscription) : μ_A (δ_A a).1 (δ_A a).2 = a := by
  unfold μ_A δ_A tensorProduct
  ext <;> simp

-- ============================================================
-- §4  Meet-diagonal Frobenius (Structure B)
--     δ_B(a) = (a, a)                — diagonal comultiplication
--     μ_B(x, y) = compute_meet(x, y)  — lattice meet (GLB)
--     Theorem: μ_B ∘ δ_B = id
-- ============================================================

/-- Diagonal comultiplication: δ_B(a) = (a, a). -/
def δ_B (a : Imscription) : Imscription × Imscription := (a, a)

/-- Meet multiplication: μ_B(x, y) = compute_meet(x, y). -/
def μ_B (x y : Imscription) : Imscription := compute_meet x y

/-- μ_B ∘ δ_B = id : meet(a, a) = a for every Imscription a. -/
theorem mu_delta_B_id (a : Imscription) : μ_B (δ_B a).1 (δ_B a).2 = a := by
  unfold μ_B δ_B compute_meet
  ext <;> simp

-- ============================================================
-- §5  Lattice-interval Frobenius (Structure D)
--     δ_D(a) = (⊥, a)                  — interval [⊥, a]
--     μ_D(x, y) = compute_join(x, y)    — lattice join (LUB)
--     Theorem: μ_D ∘ δ_D = id
-- ============================================================

/-- Interval comultiplication: δ_D(a) = (⊥, a) where ⊥ = frobenius_bottom. -/
def δ_D (a : Imscription) : Imscription × Imscription := (frobenius_bottom, a)

/-- Join multiplication: μ_D(x, y) = compute_join(x, y). -/
def μ_D (x y : Imscription) : Imscription := compute_join x y

/-- μ_D ∘ δ_D = id : join(⊥, a) = a.  Since ⊥ has all primitives at minimum,
    joining it with any a recovers a pointwise. -/
theorem mu_delta_D_id (a : Imscription) : μ_D (δ_D a).1 (δ_D a).2 = a := by
  unfold μ_D δ_D compute_join frobenius_bottom
  ext
  · -- dim
    by_cases h : compare D_wedge a.dim = .lt
    · simp [h]
    · simp [h, D_bottom_eq a.dim h]
  · -- top
    by_cases h : compare T_network a.top = .lt
    · simp [h]
    · simp [h, T_bottom_eq a.top h]
  · -- rel
    by_cases h : compare R_super a.rel = .lt
    · simp [h]
    · simp [h, R_bottom_eq a.rel h]
  · -- pol
    by_cases h : compare P_asym a.pol = .lt
    · simp [h]
    · simp [h, P_bottom_eq a.pol h]
  · -- fid
    by_cases h : compare F_ell a.fid = .lt
    · simp [h]
    · simp [h, F_bottom_eq a.fid h]
  · -- kin
    by_cases h : compare K_fast a.kin = .lt
    · simp [h]
    · simp [h, K_bottom_eq a.kin h]
  · -- gran
    by_cases h : compare G_beth a.gran = .lt
    · simp [h]
    · simp [h, G_bottom_eq a.gran h]
  · -- gram
    by_cases h : compare Gamma_and a.gram = .lt
    · simp [h]
    · simp [h, Γ_bottom_eq a.gram h]
  · -- crit
    by_cases h : compare Phi_sub a.crit = .lt
    · simp [h]
    · simp [h, Φ_bottom_eq a.crit h]
  · -- chir
    by_cases h : compare H0 a.chir = .lt
    · simp [h]
    · simp [h, H_bottom_eq a.chir h]
  · -- stoi
    by_cases h : compare one_one a.stoi = .lt
    · simp [h]
    · simp [h, S_bottom_eq a.stoi h]
  · -- prot
    by_cases h : compare Omega_0 a.prot = .lt
    · simp [h]
    · simp [h, Ω_bottom_eq a.prot h]

-- ============================================================
-- §6  Polarization Frobenius (Structure C)
--     δ_C(a) = (a_left, a_right)
--       left:  pol → P_psi, crit → Phi_sub
--       right: pol → P_sym,  crit → Phi_super
--     μ_C(x, y) = tensorProduct(x, y) with pol := P_pm_sym, crit := Phi_c
--     Theorem: μ_C ∘ δ_C = id ON the Frobenius-special class
--              (a.pol = P_pm_sym ∧ a.crit = Phi_c)
--     This mirrors the Belnap-level: B → (T, F) → ffuse → B.
-- ============================================================

/-- Polarizing comultiplication: splits along polarity and criticality axes.
    Left → quantum phase symmetry (P_psi) + subcritical (Phi_sub).
    Right → full symmetry (P_sym) + supercritical (Phi_super). -/
def δ_C (a : Imscription) : Imscription × Imscription :=
  ( { a with pol := P_psi, crit := Phi_sub },
    { a with pol := P_sym,  crit := Phi_super } )

/-- Polarization fusion: recovers Frobenius-special tuple.
    tensorProduct composes the other 10 primitives; pol and crit are
    set to P_pm_sym and Phi_c — the critical point arises from the
    tension between sub- and super-critical. -/
def μ_C (x y : Imscription) : Imscription :=
  { tensorProduct x y with
    pol  := P_pm_sym
    crit := Phi_c
  }

/-- μ_C ∘ δ_C = id on the Frobenius-special class: those a with
    pol = P_pm_sym and crit = Phi_c. -/
theorem mu_delta_C_id_on_special (a : Imscription)
    (hpol : a.pol = P_pm_sym) (hcrit : a.crit = Phi_c) :
    μ_C (δ_C a).1 (δ_C a).2 = a := by
  unfold μ_C δ_C tensorProduct
  ext <;> simp [hpol, hcrit]

/-- The Frobenius-special class is nonempty: scalarField_Kslow
    (Higgs / axion / inflaton) has pol = P_pm_sym and crit = Phi_c. -/
theorem scalarField_Kslow_is_special :
    scalarField_Kslow.pol = P_pm_sym ∧ scalarField_Kslow.crit = Phi_c := by
  unfold scalarField_Kslow; simp

/-- Corollary: μ_C ∘ δ_C = id on scalarField_Kslow. -/
theorem mu_delta_C_id_on_scalarField :
    μ_C (δ_C scalarField_Kslow).1 (δ_C scalarField_Kslow).2 = scalarField_Kslow :=
  mu_delta_C_id_on_special scalarField_Kslow
    (by unfold scalarField_Kslow; decide)
    (by unfold scalarField_Kslow; decide)

end Imscribing.Frobenius
