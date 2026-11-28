
import Imscribing.YangMills.ConcreteTensorProductSchwartz
import Imscribing.YangMills.OSBorchersBridge

/-!
# Concrete Euclidean Field Operators on a Dense Invariant Domain of `OSHilbert`
-/

namespace Imscribing.YangMills.EuclideanFieldOnOS

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
      intro z hz i
      simp only [Nat.zero_add] at i hz ⊢
      have hg' := hg (projRight 0 n z) hz i
      simpa [projRight] using hg'
  · rcases g.2 with rfl | hg
    · right
      intro z hz i
      simp only [Nat.add_zero] at i hz ⊢
      have hf' := hf (projLeft m 0 z) hz i
      simpa [projLeft] using hf'
    · right
      intro z hz i
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · exact hf (projLeft m n z) hz i₁
      · exact hg (projRight m n z) hz i₂

/-- Multiplication of a degree-`n` positive-time Schwartz element by `f : PosSchwartzSubmodule 1`. -/
noncomputable def euclidFieldMul (f : PosSchwartzSubmodule 1) (n : ℕ) :
    PosSchwartzSubmodule n →ₗ[ℂ] PosSchwartzSubmodule (1 + n) where
  toFun g := ⟨tensorSchwartz f.1 g.1, tensorSchwartz_mem_pos f g⟩
  map_add' g₁ g₂ := by ext z; simp [tensorSchwartz, mul_add]
  map_smul' c g := by ext z; simp [tensorSchwartz, smul_eq_mul]; ring

/-- Global Euclidean field creation operator on `BorchersPos := Π₀ n, PosSchwartzSubmodule n`. -/
noncomputable def borchersFieldMul (f : PosSchwartzSubmodule 1) :
    BorchersPos →ₗ[ℂ] BorchersPos where
  toFun F := F.sum fun n gn => DFinsupp.single (1 + n) (euclidFieldMul f n gn)
  map_add' F G := by
    rw [DFinsupp.sum_add_index']
    · intro n; simp
    · intro n a b; rw [map_add, DFinsupp.single_add]
  map_smul' c F := by
    simp only [DFinsupp.sum, smul_eq_mul]
    rw [Finset.smul_sum]
    have h_sub : (c • F).support ⊆ F.support := DFinsupp.support_smul
    rw [← Finset.sum_subset h_sub]
    · refine Finset.sum_congr rfl fun n _ => ?_
      simp [map_smul, DFinsupp.single_smul]
    · intro n _ hn
      have hn0 : (c • F) n = 0 := DFinsupp.not_mem_support_iff.mp hn
      simp [hn0]

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
def coeLin (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] :
    H₀ →ₗ[ℂ] UniformSpace.Completion H₀ where
  toFun x := (x : UniformSpace.Completion H₀)
  map_add' x y := UniformSpace.Completion.coe_add x y
  map_smul' c x := UniformSpace.Completion.coe_smul c x

theorem coeLin_injective (H₀ : Type*) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] :
    Function.Injective (coeLin H₀) := by
  intro x y hxy
  have h0 : (coeLin H₀ (x - y)) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hn : ‖x - y‖ = 0 := by
    rw [← UniformSpace.Completion.norm_coe]
    change ‖coeLin H₀ (x - y)‖ = 0
    rw [h0, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Dense invariant Euclidean field domain `LinearMap.range (coeLin H₀)` inside `OSHilbert`. -/
def osFieldDomain (pre : EuclideanPreData BorchersPos) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    Submodule ℂ (UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)) := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  exact LinearMap.range (coeLin (BorchersPos ⧸ nullSubmodule pre))

theorem osFieldDomain_dense (pre : EuclideanPreData BorchersPos) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    Dense ((osFieldDomain pre : Submodule ℂ _) : Set (UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre))) := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  exact UniformSpace.Completion.denseRange_coe

theorem vac_mem_osFieldDomain (pre : EuclideanPreData BorchersPos) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    ((Submodule.Quotient.mk pre.e₀ : BorchersPos ⧸ nullSubmodule pre) :
      UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)) ∈ osFieldDomain pre :=
  ⟨Submodule.Quotient.mk pre.e₀, rfl⟩

/-- Lifted Euclidean field operator `φ(f) : osFieldDomain pre →ₗ[ℂ] OSHilbert`. -/
noncomputable def euclidFieldOp (pre : EuclideanPreData BorchersPos)
    (f : PosSchwartzSubmodule 1)
    (h_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    let D := osFieldDomain pre
    { op : D →ₗ[ℂ] UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre) //
      (∀ ψ : D, op ψ ∈ D) ∧
      (∀ F : BorchersPos,
        op ⟨((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : _),
            ⟨Submodule.Quotient.mk F, rfl⟩⟩ =
          ((Submodule.Quotient.mk (borchersFieldMul f F) : BorchersPos ⧸ nullSubmodule pre) : _)) } := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  set H₀ := BorchersPos ⧸ nullSubmodule pre
  let op₀ : H₀ →ₗ[ℂ] H₀ :=
    (nullSubmodule pre).liftQ ((Submodule.mkQ (nullSubmodule pre)).comp (borchersFieldMul f))
      (fun F hF => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact borchersFieldMul_preserves_null pre f h_adj hF)
  let equivD : osFieldDomain pre ≃ₗ[ℂ] H₀ :=
    (LinearEquiv.ofInjective (coeLin H₀) (coeLin_injective H₀)).symm
  let op : osFieldDomain pre →ₗ[ℂ] UniformSpace.Completion H₀ :=
    (coeLin H₀).comp (op₀.comp equivD.toLinearMap)
  refine ⟨op, fun ψ => ⟨op₀ (equivD ψ), rfl⟩, fun F => ?_⟩
  have heq : equivD ⟨coeLin H₀ (Submodule.Quotient.mk F), ⟨Submodule.Quotient.mk F, rfl⟩⟩ =
      Submodule.Quotient.mk F := by
    apply (LinearEquiv.ofInjective (coeLin H₀) (coeLin_injective H₀)).injective
    simp [equivD]
  change coeLin H₀ (op₀ (equivD _)) = _
  rw [heq]
  rfl

/-- **Euclidean Field Commutativity on `osFieldDomain` from OS-E3 Symmetry.** -/
theorem euclidFieldOp_commute (pre : EuclideanPreData BorchersPos)
    (f g : PosSchwartzSubmodule 1)
    (hf_adj : ∃ f_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul f G) = pre.B (borchersFieldMul f_adj F) G)
    (hg_adj : ∃ g_adj : PosSchwartzSubmodule 1, ∀ F G : BorchersPos,
      pre.B F (borchersFieldMul g G) = pre.B (borchersFieldMul g_adj F) G)
    (h_e3_fg : ∀ F G : BorchersPos,
      pre.B (borchersFieldMul f (borchersFieldMul g F)) G =
      pre.B (borchersFieldMul g (borchersFieldMul f F)) G) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    let opF := euclidFieldOp pre f hf_adj
    let opG := euclidFieldOp pre g hg_adj
    ∀ ψ : osFieldDomain pre,
      opF.1 ⟨opG.1 ψ, opG.2.1 ψ⟩ =
      opG.1 ⟨opF.1 ψ, opF.2.1 ψ⟩ := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  set H₀ := BorchersPos ⧸ nullSubmodule pre
  let opF := euclidFieldOp pre f hf_adj
  let opG := euclidFieldOp pre g hg_adj
  rintro ⟨x, ⟨x₀, rfl⟩⟩
  induction x₀ using Submodule.Quotient.induction_on with
  | _ F =>
    have h1 : (⟨opG.1 ⟨coeLin H₀ (Submodule.Quotient.mk F), ⟨Submodule.Quotient.mk F, rfl⟩⟩,
        opG.2.1 _⟩ : osFieldDomain pre) =
        ⟨coeLin H₀ (Submodule.Quotient.mk (borchersFieldMul g F)),
          ⟨Submodule.Quotient.mk (borchersFieldMul g F), rfl⟩⟩ := by
      apply Subtype.ext; exact opG.2.2 F
    have h2 : (⟨opF.1 ⟨coeLin H₀ (Submodule.Quotient.mk F), ⟨Submodule.Quotient.mk F, rfl⟩⟩,
        opF.2.1 _⟩ : osFieldDomain pre) =
        ⟨coeLin H₀ (Submodule.Quotient.mk (borchersFieldMul f F)),
          ⟨Submodule.Quotient.mk (borchersFieldMul f F), rfl⟩⟩ := by
      apply Subtype.ext; exact opF.2.2 F
    change opF.1 ⟨opG.1 ⟨coeLin H₀ (Submodule.Quotient.mk F), _⟩, _⟩ =
      opG.1 ⟨opF.1 ⟨coeLin H₀ (Submodule.Quotient.mk F), _⟩, _⟩
    rw [h1, h2, opF.2.2 (borchersFieldMul g F), opG.2.2 (borchersFieldMul f F)]
    congr 1
    apply Submodule.Quotient.eq.mpr
    change (pre.B (borchersFieldMul f (borchersFieldMul g F) -
        borchersFieldMul g (borchersFieldMul f F))
      (borchersFieldMul f (borchersFieldMul g F) -
        borchersFieldMul g (borchersFieldMul f F))).re = 0
    set X := borchersFieldMul f (borchersFieldMul g F) - borchersFieldMul g (borchersFieldMul f F)
    have hX : ∀ G : BorchersPos, pre.B X G = 0 := by
      intro G
      have hs : X = borchersFieldMul f (borchersFieldMul g F) +
          (-1 : ℂ) • borchersFieldMul g (borchersFieldMul f F) := by
        dsimp [X]; rw [sub_eq_add_neg]; simp
      rw [hs, pre.B_add_left, pre.B_smul_left, h_e3_fg F G]
      simp
    rw [hX X, Complex.zero_re]

end Imscribing.YangMills.EuclideanFieldOnOS