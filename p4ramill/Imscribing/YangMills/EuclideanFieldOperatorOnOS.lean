
import Imscribing.YangMills.ConcreteTensorProductSchwartz
import Imscribing.YangMills.OSBorchersBridge

/-!
# Concrete Euclidean Field Operators on a Dense Invariant Domain of `OSHilbert`
-/

namespace Imscribing.YangMills.EuclideanFieldOnOS

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.OSCompletion
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.ConcreteTensorSchwartz

theorem tensorSchwartz_mem_pos {m n : ℕ}
    (f : PosSchwartzSubmodule m) (g : PosSchwartzSubmodule n) :
    tensorSchwartz f.1 g.1 ∈ PosSchwartzSubmodule (m + n) := by
  rcases f.2 with rfl | hf
  · rcases g.2 with rfl | hg
    · exact Or.inl rfl
    · right
      intro z hz i; let j : Fin n := ⟨i.1, by omega⟩; have hj : projRight 0 n z j = z i := congrArg z (Fin.ext (by simp [j])); rw [← hj]; exact hg (projRight 0 n z) (right_ne_zero_of_mul (by change f.1 (projLeft _ _ z) * g.1 (projRight _ _ z) ≠ 0; exact hz)) j
  · rcases g.2 with rfl | hg
    · right
      intro z hz i; let j : Fin m := ⟨i.1, by omega⟩; have hj : projLeft m 0 z j = z i := congrArg z (Fin.ext rfl); rw [← hj]; exact hf (projLeft m 0 z) (left_ne_zero_of_mul (by change f.1 (projLeft _ _ z) * g.1 (projRight _ _ z) ≠ 0; exact hz)) j
    · right
      intro z hz i
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · exact hf (projLeft m n z) (left_ne_zero_of_mul (by change f.1 (projLeft _ _ z) * g.1 (projRight _ _ z) ≠ 0; exact hz)) i₁
      · exact hg (projRight m n z) (right_ne_zero_of_mul (by change f.1 (projLeft _ _ z) * g.1 (projRight _ _ z) ≠ 0; exact hz)) i₂

/-- Multiplication of a degree-`n` positive-time Schwartz element by `f : PosSchwartzSubmodule 1`. -/
noncomputable def euclidFieldMul (f : PosSchwartzSubmodule 1) (n : ℕ) :
    PosSchwartzSubmodule n →ₗ[ℂ] PosSchwartzSubmodule (1 + n) where
  toFun g := ⟨tensorSchwartz f.1 g.1, tensorSchwartz_mem_pos f g⟩
  map_add' g₁ g₂ := by ext z; change f.1 (projLeft 1 n z) * (g₁.1 + g₂.1) (projRight 1 n z) = f.1 (projLeft 1 n z) * g₁.1 (projRight 1 n z) + f.1 (projLeft 1 n z) * g₂.1 (projRight 1 n z); simp [mul_add]
  map_smul' c g := by ext z; change f.1 (projLeft 1 n z) * (c • g.1) (projRight 1 n z) = c * (f.1 (projLeft 1 n z) * g.1 (projRight 1 n z)); simp [smul_eq_mul]; ring

/-- Global Euclidean field creation operator on `BorchersPos := Π₀ n, PosSchwartzSubmodule n`. -/
noncomputable def borchersFieldMul (f : PosSchwartzSubmodule 1) :
    BorchersPos →ₗ[ℂ] BorchersPos where
  toFun F := F.sum fun n gn => DFinsupp.single (1 + n) (euclidFieldMul f n gn)
  map_add' F G := by
    classical
    let φ : ∀ n, PosSchwartzSubmodule n →+ BorchersPos := fun n => (DFinsupp.singleAddHom (β := fun k => PosSchwartzSubmodule k) (1 + n)).comp (euclidFieldMul f n).toAddMonoidHom
    change (DFinsupp.sum (F + G) fun n => ⇑(φ n).toZeroHom) = (DFinsupp.sum F fun n => ⇑(φ n).toZeroHom) + (DFinsupp.sum G fun n => ⇑(φ n).toZeroHom)
    rw [← DFinsupp.sumZeroHom_apply (fun n => (φ n).toZeroHom) (F + G), ← DFinsupp.sumZeroHom_apply (fun n => (φ n).toZeroHom) F, ← DFinsupp.sumZeroHom_apply (fun n => (φ n).toZeroHom) G]; exact (DFinsupp.sumAddHom φ).map_add F G
  map_smul' c F := by
    simp only [DFinsupp.sum, smul_eq_mul]
    rw [Finset.smul_sum]
    have h_sub : (c • F).support ⊆ F.support := DFinsupp.support_smul c F
    rw [← Finset.sum_subset h_sub]
    · refine Finset.sum_congr rfl fun n _ => ?_
      simp [map_smul, DFinsupp.single_smul]
    · intro n _ hn
      by_cases hc : c = 0
      · simp [hc]
      · have h0 : F n = 0 := (show c ≠ 0 → F n = 0 by simpa [DFinsupp.mem_support_iff] using hn) hc; simp [h0]

/-- Null-space invariance of `borchersFieldMul f` via `sesquilinear_cauchy_schwarz`. -/
theorem borchersFieldMul_preserves_null
    (pre : EuclideanPreData BorchersPos) (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    {F : BorchersPos} (hF : F ∈ nullSubmodule pre) :
    borchersFieldMul f F ∈ nullSubmodule pre := by
  obtain ⟨f_adj, hadj⟩ := h_adj
  change (pre.B (borchersFieldMul f F) (borchersFieldMul f F)).re = 0
  rw [hadj (borchersFieldMul f F) F]
  have hcs := sesquilinear_cauchy_schwarz pre.B pre.B_add_left pre.B_smul_left
    pre.B_add_right pre.B_smul_right pre.B_herm pre.B_nonneg
    (borchersFieldMul f_adj (borchersFieldMul f F)) F
  have hF_re : (pre.B F F).re = 0 := hF
  rw [hF_re, mul_zero] at hcs
  have h0 : pre.B (borchersFieldMul f_adj (borchersFieldMul f F)) F = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg (pre.B (borchersFieldMul f_adj (borchersFieldMul f F)) F)])
  rw [h0, Complex.zero_re]

/-- Linear canonical embedding `H₀ →ₗ[ℂ] Completion H₀`. -/
def coeLin (H₀ : Type*) [NormedAddCommGroup H₀] [NormedSpace ℂ H₀] :
    H₀ →ₗ[ℂ] UniformSpace.Completion H₀ where
  toFun x := (x : UniformSpace.Completion H₀)
  map_add' x y := UniformSpace.Completion.coe_add x y
  map_smul' c x := UniformSpace.Completion.coe_smul c x

theorem coeLin_injective (H₀ : Type*) [NormedAddCommGroup H₀] [NormedSpace ℂ H₀] :
    Function.Injective (coeLin H₀) := by
  intro x y hxy
  have h0 : (coeLin H₀ (x - y)) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hn : ‖x - y‖ = 0 := by
    rw [← UniformSpace.Completion.norm_coe]
    change ‖coeLin H₀ (x - y)‖ = 0
    rw [h0, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

section
set_option maxSynthPendingDepth 1
set_option maxHeartbeats 400000

private noncomputable local instance (pre : EuclideanPreData BorchersPos) :
    NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) :=
  (quotInnerCore pre).toNormedAddCommGroup

private noncomputable local instance (pre : EuclideanPreData BorchersPos) :
    NormedSpace ℂ (BorchersPos ⧸ nullSubmodule pre) :=
  (@InnerProductSpace.ofCore ℂ (BorchersPos ⧸ nullSubmodule pre) _
    (Submodule.Quotient.addCommGroup _) (Submodule.Quotient.module _)
    (quotInnerCore pre).toCore).toNormedSpace

/-- Dense invariant Euclidean field domain `LinearMap.range (coeLin H₀)` inside `OSHilbert`. -/
noncomputable def osFieldDomain (pre : EuclideanPreData BorchersPos) :
    Submodule ℂ (UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)) :=
  LinearMap.range (coeLin (BorchersPos ⧸ nullSubmodule pre))

theorem osFieldDomain_dense (pre : EuclideanPreData BorchersPos) :
    Dense ((osFieldDomain pre : Submodule ℂ _) :
      Set (UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre))) :=
  UniformSpace.Completion.denseRange_coe

theorem vac_mem_osFieldDomain (pre : EuclideanPreData BorchersPos) :
    (coeLin (BorchersPos ⧸ nullSubmodule pre)) (Submodule.Quotient.mk pre.e₀) ∈
      osFieldDomain pre :=
  ⟨Submodule.Quotient.mk pre.e₀, rfl⟩

private noncomputable def euclidOpQuot (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G) :
    (BorchersPos ⧸ nullSubmodule pre) →ₗ[ℂ] (BorchersPos ⧸ nullSubmodule pre) :=
  let mf := borchersFieldMul f
  { toFun := fun x => Quotient.liftOn' x
      (fun F => (Submodule.Quotient.mk (mf F) : (BorchersPos ⧸ nullSubmodule pre)))
      fun a b hab => (Submodule.Quotient.eq (nullSubmodule pre)).mpr <| by
        have hs : a - b ∈ nullSubmodule pre :=
          (Submodule.Quotient.eq (nullSubmodule pre)).mp (Quotient.sound hab)
        change mf a - mf b ∈ nullSubmodule pre
        rw [← map_sub mf]
        exact borchersFieldMul_preserves_null pre f h_adj hs
    map_add' := fun x y => by
      induction x using Submodule.Quotient.induction_on with | _ a =>
      induction y using Submodule.Quotient.induction_on with | _ b =>
      exact congrArg Submodule.Quotient.mk (map_add mf a b)
    map_smul' := fun c x => by
      induction x using Submodule.Quotient.induction_on with | _ a =>
      exact congrArg Submodule.Quotient.mk (map_smul mf c a) }

private noncomputable def equivD (pre : EuclideanPreData BorchersPos) :
    osFieldDomain pre ≃ₗ[ℂ] (BorchersPos ⧸ nullSubmodule pre) :=
  (LinearEquiv.ofInjective (coeLin (BorchersPos ⧸ nullSubmodule pre))
    (coeLin_injective (BorchersPos ⧸ nullSubmodule pre))).symm

private theorem equivD_mk (pre : EuclideanPreData BorchersPos)
    (x : BorchersPos ⧸ nullSubmodule pre)
    (hx : coeLin (BorchersPos ⧸ nullSubmodule pre) x ∈ osFieldDomain pre) :
    equivD pre ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) x, hx⟩ = x :=
  (LinearEquiv.ofInjective (coeLin (BorchersPos ⧸ nullSubmodule pre))
    (coeLin_injective (BorchersPos ⧸ nullSubmodule pre))).symm_apply_apply x

private noncomputable def euclidFieldOpFun (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G) :
    osFieldDomain pre →ₗ[ℂ] UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre) :=
  (coeLin (BorchersPos ⧸ nullSubmodule pre)).comp
    ((euclidOpQuot pre f h_adj).comp (equivD pre).toLinearMap)

private theorem euclidFieldOpFun_mem (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    (ψ : osFieldDomain pre) : euclidFieldOpFun pre f h_adj ψ ∈ osFieldDomain pre :=
  ⟨_, rfl⟩

private theorem euclidFieldOpFun_apply_mk (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    (F : BorchersPos)
    (hmem : coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F) ∈ osFieldDomain pre) :
    euclidFieldOpFun pre f h_adj
      ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), hmem⟩ =
      coeLin (BorchersPos ⧸ nullSubmodule pre)
        (Submodule.Quotient.mk (borchersFieldMul f F)) := by
  change coeLin (BorchersPos ⧸ nullSubmodule pre)
    (euclidOpQuot pre f h_adj (equivD pre ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), hmem⟩)) = _
  rw [equivD_mk pre (Submodule.Quotient.mk F) hmem]
  rfl

noncomputable def euclidFieldOp (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G) :
    { op : osFieldDomain pre →ₗ[ℂ]
        UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre) //
      (∀ ψ : osFieldDomain pre, op ψ ∈ osFieldDomain pre) ∧
      (∀ F : BorchersPos,
        op ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), ⟨_, rfl⟩⟩ =
          coeLin (BorchersPos ⧸ nullSubmodule pre)
            (Submodule.Quotient.mk (borchersFieldMul f F))) } :=
  ⟨euclidFieldOpFun pre f h_adj, euclidFieldOpFun_mem pre f h_adj,
    fun F => euclidFieldOpFun_apply_mk pre f h_adj F ⟨_, rfl⟩⟩

private theorem euclidFieldOpFun_comp_mk (pre : EuclideanPreData BorchersPos)
    (f g : PosSchwartzSubmodule 1)
    (hf_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    (hg_adj : ∃ g_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul g G) = pre.B (borchersFieldMul g_adj F) G)
    (F : BorchersPos)
    (hmem : coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F) ∈ osFieldDomain pre) :
    euclidFieldOpFun pre f hf_adj
      ⟨euclidFieldOpFun pre g hg_adj
        ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), hmem⟩,
        euclidFieldOpFun_mem pre g hg_adj _⟩ =
      coeLin (BorchersPos ⧸ nullSubmodule pre)
        (Submodule.Quotient.mk (borchersFieldMul f (borchersFieldMul g F))) := by
  have h1 : euclidFieldOpFun pre g hg_adj
      ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), hmem⟩ =
      coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk (borchersFieldMul g F)) :=
    euclidFieldOpFun_apply_mk pre g hg_adj F hmem
  have h2 : (⟨euclidFieldOpFun pre g hg_adj
        ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk F), hmem⟩,
      euclidFieldOpFun_mem pre g hg_adj _⟩ : osFieldDomain pre) =
      ⟨coeLin (BorchersPos ⧸ nullSubmodule pre) (Submodule.Quotient.mk (borchersFieldMul g F)),
        ⟨Submodule.Quotient.mk (borchersFieldMul g F), rfl⟩⟩ :=
    Subtype.ext h1
  exact (congrArg (euclidFieldOpFun pre f hf_adj) h2).trans
    (euclidFieldOpFun_apply_mk pre f hf_adj (borchersFieldMul g F) ⟨_, rfl⟩)

theorem euclidFieldOp_commute (pre : EuclideanPreData BorchersPos) (f g : PosSchwartzSubmodule 1)
    (hf_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    (hg_adj : ∃ g_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul g G) = pre.B (borchersFieldMul g_adj F) G)
    (h_e3_fg : ∀ F G : BorchersPos,
      pre.B (borchersFieldMul f (borchersFieldMul g F)) G =
      pre.B (borchersFieldMul g (borchersFieldMul f F)) G) :
    ∀ ψ : osFieldDomain pre,
      (euclidFieldOp pre f hf_adj).1
        ⟨(euclidFieldOp pre g hg_adj).1 ψ, (euclidFieldOp pre g hg_adj).2.1 ψ⟩ =
      (euclidFieldOp pre g hg_adj).1
        ⟨(euclidFieldOp pre f hf_adj).1 ψ, (euclidFieldOp pre f hf_adj).2.1 ψ⟩ := by
  rintro ⟨x, ⟨x₀, rfl⟩⟩
  induction x₀ using Submodule.Quotient.induction_on with | _ F =>
  have hL := euclidFieldOpFun_comp_mk pre f g hf_adj hg_adj F ⟨Submodule.Quotient.mk F, rfl⟩
  have hR := euclidFieldOpFun_comp_mk pre g f hg_adj hf_adj F ⟨Submodule.Quotient.mk F, rfl⟩
  have hM : coeLin (BorchersPos ⧸ nullSubmodule pre)
        (Submodule.Quotient.mk (borchersFieldMul f (borchersFieldMul g F))) =
      coeLin (BorchersPos ⧸ nullSubmodule pre)
        (Submodule.Quotient.mk (borchersFieldMul g (borchersFieldMul f F))) := by
    refine congrArg (coeLin (BorchersPos ⧸ nullSubmodule pre))
      ((Submodule.Quotient.eq (nullSubmodule pre)).mpr ?_)
    set X := borchersFieldMul f (borchersFieldMul g F) - borchersFieldMul g (borchersFieldMul f F)
    have hX : ∀ G : BorchersPos, pre.B X G = 0 := fun G => by
      have hs : X = borchersFieldMul f (borchersFieldMul g F) +
          (-1 : ℂ) • borchersFieldMul g (borchersFieldMul f F) := by
        dsimp [X]; rw [sub_eq_add_neg]; simp
      rw [hs, pre.B_add_left, pre.B_smul_left, h_e3_fg F G]; simp
    exact show (pre.B X X).re = 0 by rw [hX X, Complex.zero_re]
  exact hL.trans (hM.trans hR.symm)
end
end Imscribing.YangMills.EuclideanFieldOnOS
