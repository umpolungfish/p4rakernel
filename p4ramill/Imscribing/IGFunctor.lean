-- Imscribing/IGFunctor.lean
-- Formal functor from IG_Cat to established mathematical structures.
--
-- Main results:
--   TierFunctor : Imscription ⥤ OuroboricityTier
--     CategoryTheory.Functor between the tier-preorder category on
--     Imscription and the 5-level OuroboricityTier poset.
--     Built via OrderHom.toFunctor; functoriality is free (thin category).
--
--   igFrobeniusAlg : FrobeniusAlg Imscription
--     Diagonal Frobenius algebra: delta(a)=(a,a), mu=tensorProduct, unit=odotOperator.
--     mu ∘ delta = id proved by mu_delta_A_id (0 sorrys in that theorem).
--
--   TierFunctor_Frobenius_cliff
--     A tensor product with any sub-Frobenius factor cannot reach O_inf.
--
--   O_inf_tensor_closed
--     The O_inf fiber is closed under tensor product.
--
--   Section 6: IGProtocol-level delta/mu witnesses via paralogical axioms.
--   igProtoCopy_isDagger is the one non-derived structural axiom in this file.

import Imscribing.IGMorphism
import Imscribing.Frobenius
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Hom.Basic

namespace Imscribing

open Primitives Frobenius
open CategoryTheory
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 1: OuroboricityTier PartialOrder
-- Embed into ℕ: O₀↦0, O₁↦1, O₂↦2, O₂dag↦3, O_inf↦4.
-- Single PartialOrder instance to avoid Preorder diamond.
-- ─────────────────────────────────────────────────────────────────────────────

-- Plain function (not dot notation) to avoid namespace collision with
-- Imscribing.Primitives.OuroboricityTier.
def tierToNat : OuroboricityTier → ℕ
  | .O₀    => 0
  | .O₁    => 1
  | .O₂    => 2
  | .O₂dag => 3
  | .O_inf => 4

theorem tierToNat_injective : Function.Injective tierToNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [tierToNat]

-- Single declaration: PartialOrder (which includes Preorder).
-- No separate LT field — use Preorder default (a < b := a ≤ b ∧ ¬b ≤ a).
instance igTierPartialOrder : PartialOrder OuroboricityTier where
  le a b          := tierToNat a ≤ tierToNat b
  le_refl a       := Nat.le_refl _
  le_trans a b c  := Nat.le_trans
  le_antisymm a b h₁ h₂ := tierToNat_injective (Nat.le_antisymm h₁ h₂)

instance (a b : OuroboricityTier) : Decidable (a ≤ b) :=
  Nat.decLe (tierToNat a) (tierToNat b)

theorem tier_O₀_le_all (t : OuroboricityTier) : .O₀ ≤ t :=
  Nat.zero_le _

theorem tier_all_le_O_inf (t : OuroboricityTier) : t ≤ .O_inf := by
  cases t <;> decide

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 2: Imscription tier-preorder
-- a ≤ b iff imscriptionTier a ≤ imscriptionTier b.
-- ─────────────────────────────────────────────────────────────────────────────

instance igImscriptionPreorder : Preorder Imscription where
  le a b         := imscriptionTier a ≤ imscriptionTier b
  le_refl a      := le_refl _
  le_trans a b c := le_trans

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 3: TierFunctor : Imscription ⥤ OuroboricityTier
-- ─────────────────────────────────────────────────────────────────────────────

/-- imscriptionTier as a monotone map between preorder types. -/
def tierOrderHom : Imscription →o OuroboricityTier where
  toFun      := imscriptionTier
  monotone'  := fun {_ _} h => h

/-- TierFunctor: CategoryTheory.Functor between preorder-induced small categories. -/
def TierFunctor : Imscription ⥤ OuroboricityTier :=
  tierOrderHom.toFunctor

@[simp] theorem TierFunctor_obj (a : Imscription) :
    TierFunctor.obj a = imscriptionTier a := rfl

-- Functoriality is free: hom-sets in preorder categories are subsingletons.
theorem TierFunctor_map_id (a : Imscription) :
    TierFunctor.map (𝟙 a) = 𝟙 (TierFunctor.obj a) :=
  Subsingleton.elim _ _

theorem TierFunctor_map_comp {a b c : Imscription} (f : a ⟶ b) (g : b ⟶ c) :
    TierFunctor.map (f ≫ g) = TierFunctor.map f ≫ TierFunctor.map g :=
  Subsingleton.elim _ _

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 4: Structural theorems
-- ─────────────────────────────────────────────────────────────────────────────

/-- O_inf fiber is exactly the Frobenius locus. -/
theorem TierFunctor_O_inf_fiber (a : Imscription) :
    TierFunctor.obj a = .O_inf ↔
    (a.crit = .Phi_c ∨ a.crit = .Phi_c_complex) ∧ a.pol = .P_pm_sym :=
  o_inf_iff_P_pm_sym_at_phi_c a

/-- Frobenius cliff: no tensor product with a sub-Frobenius factor reaches O_inf. -/
theorem TierFunctor_Frobenius_cliff (a b : Imscription)
    (ha : a.pol ≠ .P_pm_sym) :
    TierFunctor.obj (tensorProduct a b) ≠ .O_inf := by
  simp only [TierFunctor_obj]
  intro h
  have hpol : polarityTensor a.pol b.pol = P_pm_sym :=
    ((o_inf_iff_P_pm_sym_at_phi_c _).mp h).2
  exact frobenius_not_synthesizable a.pol b.pol ha hpol

/-- The O_inf fiber is closed under tensor product. -/
theorem O_inf_tensor_closed (a b : Imscription)
    (ha : imscriptionTier a = .O_inf)
    (hb : imscriptionTier b = .O_inf) :
    imscriptionTier (tensorProduct a b) = .O_inf := by
  rw [o_inf_iff_P_pm_sym_at_phi_c] at ha hb ⊢
  obtain ⟨ha_crit, ha_pol⟩ := ha
  obtain ⟨hb_crit, hb_pol⟩ := hb
  -- tensorProduct fields are accessible by rfl (struct literal definition).
  have hcrit_eq : (tensorProduct a b).crit =
      if compare a.crit b.crit = .lt then b.crit else a.crit := rfl
  have hpol_eq  : (tensorProduct a b).pol =
      if compare a.pol b.pol = .lt then a.pol else b.pol := rfl
  constructor
  · rw [hcrit_eq]
    split_ifs with h
    · exact hb_crit
    · exact ha_crit
  · rw [hpol_eq]
    split_ifs
    · exact ha_pol
    · exact hb_pol

/-- Every tier is inhabited (TierFunctor is surjective on objects). -/
theorem TierFunctor_surjective (t : OuroboricityTier) :
    ∃ a : Imscription, TierFunctor.obj a = t := by
  cases t with
  | O₀    => exact ⟨frobenius_bottom, by decide⟩
  | O_inf => exact ⟨quantum_gravity, by rw [TierFunctor_obj]; exact qg_is_O_inf⟩
  -- ouroboricityTier: O₁=(Phi_c, pol≠P_pm_sym, prot=Omega_0)
  --                   O₂=(Phi_c, pol≠P_pm_sym, prot≠Omega_0, dim≠D_infty)
  --                   O₂dag=(Phi_c, pol≠P_pm_sym, prot≠Omega_0, dim=D_infty)
  | O₁    => exact ⟨{ frobenius_bottom with crit := .Phi_c }, by decide⟩
  | O₂    => exact ⟨{ frobenius_bottom with crit := .Phi_c, prot := .Omega_Z }, by decide⟩
  | O₂dag =>
    exact ⟨{ frobenius_bottom with crit := .Phi_c, prot := .Omega_Z, dim := .D_infty },
      by decide⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 5: FrobeniusAlg
-- ─────────────────────────────────────────────────────────────────────────────

/-- A special Frobenius algebra structure. -/
structure FrobeniusAlg (α : Type*) where
  mul : α → α → α
  comul : α → α × α
  unit : α
  frob : ∀ a, mul (comul a).1 (comul a).2 = a

/-- Canonical diagonal Frobenius algebra on Imscription.
    mu_delta_A_id (0 sorrys in Frobenius.lean) closes the frob field. -/
def igFrobeniusAlg : FrobeniusAlg Imscription where
  mul   := tensorProduct
  comul := fun a => (a, a)
  unit  := odotOperator
  frob  := mu_delta_A_id

theorem igFrobAlg_self_fusion (a : Imscription) :
    igFrobeniusAlg.mul a a = a :=
  mu_delta_A_id a

-- odotOperator is the canonical O_inf element; its tier is decidable.
theorem igFrobAlg_unit_is_O_inf :
    TierFunctor.obj igFrobeniusAlg.unit = .O_inf := by
  simp only [igFrobeniusAlg, TierFunctor_obj]
  decide

theorem igFrobAlg_unit_at_top :
    ∀ a : Imscription, TierFunctor.obj a ≤ TierFunctor.obj igFrobeniusAlg.unit := by
  intro a
  rw [igFrobAlg_unit_is_O_inf]
  simp only [TierFunctor_obj]
  exact tier_all_le_O_inf _

-- ─────────────────────────────────────────────────────────────────────────────
-- SECTION 6: IGProtocol-level Frobenius witnesses
-- paralogical_copy produces delta : s → s ⊗ s as an IGProtocol morphism.
-- igProtoCopy_isDagger is the one non-derived axiom in this file.
-- ─────────────────────────────────────────────────────────────────────────────

open IGProtocol

noncomputable def igProtoDelta (s : Imscription) (h : imscriptionTier s = .O_inf) :
    IGProtocol s (tensorProduct s s) :=
  (paralogical_copy h).val

theorem igProtoDelta_depth (s : Imscription) (h : imscriptionTier s = .O_inf) :
    (igProtoDelta s h).depth = 1 :=
  (paralogical_copy h).property

/-- The O_inf copy protocol carries R_dagger labels; this enables
    paralogical_dagger to produce mu = delta†. -/
axiom igProtoCopy_isDagger (s : Imscription) (h : imscriptionTier s = .O_inf) :
    (igProtoDelta s h).isDagger = true

noncomputable def igProtoMu (s : Imscription) (h : imscriptionTier s = .O_inf) :
    IGProtocol (tensorProduct s s) s :=
  paralogical_dagger (igProtoDelta s h) (igProtoCopy_isDagger s h)

theorem igProtoMu_depth (s : Imscription) (h : imscriptionTier s = .O_inf) :
    (igProtoMu s h).depth = 1 := by
  simp only [igProtoMu]
  rw [paralogical_dagger_depth]
  exact igProtoDelta_depth s h

end Imscribing
