import Mathlib
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.Wilson4DOp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §41.  4D Feynman–Kac slice decomposition & Euclidean spatial translations -/

section Wilson4DFeynmanKacAndSpatialTrans

/-- 4D gauge field sliced into `Lt` spatial slices (`cubicTorus3 Ls`) and `Lt` temporal gauge links. -/
def slice4DFieldEquiv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃
      (Fin Lt → GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (Fin Lt → GaugeGrp3 Ls N) where
  toFun U :=
    (fun t e => match e.2 with
      | 0 => U ((t, e.1.1, e.1.2.1, e.1.2.2), 1)
      | 1 => U ((t, e.1.1, e.1.2.1, e.1.2.2), 2)
      | 2 => U ((t, e.1.1, e.1.2.1, e.1.2.2), 3),
     fun t x => U ((t, x.1, x.2.1, x.2.2), 0))
  invFun p e := match e.2 with
    | 0 => p.2 e.1.1 (e.1.2.1, e.1.2.2.1, e.1.2.2.2)
    | 1 => p.1 e.1.1 ((e.1.2.1, e.1.2.2.1, e.1.2.2.2), 0)
    | 2 => p.1 e.1.1 ((e.1.2.1, e.1.2.2.1, e.1.2.2.2), 1)
    | 3 => p.1 e.1.1 ((e.1.2.1, e.1.2.2.1, e.1.2.2.2), 2)
  left_inv U := by
    funext ⟨⟨t, x, y, z⟩, d⟩
    fin_cases d <;> rfl
  right_inv p := by
    refine Prod.ext (funext fun t => funext fun ⟨⟨x, y, z⟩, d⟩ => ?_)
      (funext fun t => funext fun ⟨x, y, z⟩ => rfl)
    fin_cases d <;> rfl

/--
Closed spatial Polyakov loop along axis `0` on `cubicTorus3 L`:
yields a continuous, non-constant, locally gauge-invariant observable for `N ≥ 2`.
-/
def polyakovLoop3 (L : ℕ) [NeZero L] : List ((cubicTorus3 L).Link × Bool) :=
  List.ofFn fun k : Fin L => (((⟨k.val, k.isLt⟩, 0, 0), 0), true)

theorem polyakovLoop3_isPath (L : ℕ) [NeZero L] :
    IsLatticePath (cubicTorus3 L) (0, 0, 0) (0, 0, 0) (polyakovLoop3 L) := by
  have h_gen : ∀ (m : ℕ) (k0 : Fin L), k0.val + m = L →
      IsLatticePath (cubicTorus3 L) (k0, 0, 0) (0, 0, 0)
        (List.ofFn fun j : Fin m =>
          (((⟨(k0.val + j.val) % L, Nat.mod_lt _ (NeZero.pos L)⟩, 0, 0), 0), true)) := by
    intro m
    induction m with
    | zero =>
      intro k0 hm
      have hk0 : k0 = 0 := Fin.ext (by omega)
      subst hk0
      simp only [List.ofFn_zero]
      exact IsLatticePath.nil (L := cubicTorus3 L) (0, 0, 0)
    | succ m ih =>
      intro k0 hm
      by_cases hm0 : m = 0
      · subst hm0
        have hk0 : k0.val + 1 = L := hm
        have hsrc : (cubicTorus3 L).src ((k0, 0, 0), 0) = (k0, 0, 0) := rfl
        have hdst : (cubicTorus3 L).dst ((k0, 0, 0), 0) = (0, 0, 0) := by
          dsimp [cubicTorus3, cubicShift]
          congr 1; congr 1
          apply Fin.ext
          have h1 : (1 : Fin L).val = 1 % L := rfl
          rw [Fin.val_add, Fin.val_zero, h1, Nat.add_mod_mod, hk0, Nat.mod_self]
        have hk_eq0 : (⟨(k0.val + (0 : Fin 1).val) % L,
            Nat.mod_lt _ (NeZero.pos L)⟩ : Fin L) = k0 := by
          apply Fin.ext; simp [Nat.mod_eq_of_lt k0.isLt]
        rw [List.ofFn_succ, List.ofFn_zero, hk_eq0]
        exact IsLatticePath.fwd (L := cubicTorus3 L) ((k0, 0, 0), 0) [] hsrc hdst
          (IsLatticePath.nil (L := cubicTorus3 L) (0, 0, 0))
      · let k1 : Fin L := ⟨(k0.val + 1) % L, Nat.mod_lt _ (NeZero.pos L)⟩
        have hsrc : (cubicTorus3 L).src ((k0, 0, 0), 0) = (k0, 0, 0) := rfl
        have hdst : (cubicTorus3 L).dst ((k0, 0, 0), 0) = (k1, 0, 0) := by
          dsimp [cubicTorus3, cubicShift, k1]
          congr 1; congr 1
          apply Fin.ext
          have h1 : (1 : Fin L).val = 1 % L := rfl
          rw [Fin.val_add, h1, Nat.add_mod_mod]
        have hk_eq0 : (⟨(k0.val + (0 : Fin (m + 1)).val) % L,
            Nat.mod_lt _ (NeZero.pos L)⟩ : Fin L) = k0 := by
          apply Fin.ext; simp [Nat.mod_eq_of_lt k0.isLt]
        have hlt : k0.val + 1 < L := by omega
        have hk1_sum : k1.val + m = L := by
          dsimp [k1]; rw [Nat.mod_eq_of_lt hlt]; omega
        rw [List.ofFn_succ, hk_eq0]
        have h_fwd := IsLatticePath.fwd (L := cubicTorus3 L) ((k0, 0, 0), 0) _ hsrc hdst
          (ih k1 hk1_sum)
        convert h_fwd using 2
        apply congrArg List.ofFn
        funext j
        have hfin : (⟨(k0.val + j.succ.val) % L, Nat.mod_lt _ (NeZero.pos L)⟩ : Fin L) =
            ⟨(k1.val + j.val) % L, Nat.mod_lt _ (NeZero.pos L)⟩ := by
          apply Fin.ext
          dsimp [k1]
          rw [Nat.mod_eq_of_lt hlt]
          congr 1
          omega
        exact congrArg (fun x : Fin L => (((x, 0, 0), 0), true)) hfin
  have h0 := h_gen L 0 (by simp)
  have h_list_eq :
      (List.ofFn fun j : Fin L =>
          (((⟨((0 : Fin L).val + j.val) % L, Nat.mod_lt _ (NeZero.pos L)⟩, 0, 0), 0), true)) =
        polyakovLoop3 L := by
    dsimp [polyakovLoop3]; congr 1; funext j; congr 3; apply Fin.ext
    simp [Nat.mod_eq_of_lt j.isLt]
  rwa [h_list_eq] at h0

/-- Continuous, locally gauge-invariant, non-constant Polyakov observable `Re Tr(W_γ)` on `cubicTorus3 L`. -/
noncomputable def polyakovObs3 (L N : ℕ) [NeZero L]
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  (Matrix.trace ((pathHolonomy U (polyakovLoop3 L) : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ)).re

theorem polyakovObs3_gauge_inv (L N : ℕ) [NeZero L]
    (g : GaugeGrp3 L N)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    polyakovObs3 L N (gaugeAct g U) = polyakovObs3 L N U := by
  unfold polyakovObs3
  have hc := wilsonLoop_gauge_invariant
    (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Matrix.trace (M : Matrix (Fin N) (Fin N) ℂ))
    su_trace_conj' g U (polyakovLoop3_isPath L)
  exact congrArg Complex.re hc

theorem polyakovObs3_nonconst (L N : ℕ) [NeZero L] (hN : 2 ≤ N) :
    let U₁ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) := fun _ => 1
    let e₀ : (cubicTorus3 L).Link := ((0, 0, 0), 0)
    let U₂ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
      fun e => if e = e₀ then suFlip2 N hN else 1
    polyakovObs3 L N U₁ = (N : ℝ) ∧ polyakovObs3 L N U₂ = (N : ℝ) - 4 := by
  intro U₁ e₀ U₂
  have h1 : pathHolonomy U₁ (polyakovLoop3 L) = 1 := by
    have h_gen : ∀ (γ : List ((cubicTorus3 L).Link × Bool)),
        (∀ p ∈ γ, p.2 = true) → pathHolonomy U₁ γ = 1 := by
      intro γ hγ
      induction γ with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨e, b⟩
        have hb : b = true := hγ (e, b) (by simp)
        subst hb
        simp [pathHolonomy, U₁, ih (fun p hp => hγ p (by simp [hp]))]
    exact h_gen (polyakovLoop3 L) (fun p hp => by
      dsimp [polyakovLoop3] at hp
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨k, rfl⟩
      rfl)
  have h2 : pathHolonomy U₂ (polyakovLoop3 L) = suFlip2 N hN := by
    have hL : 0 < L := NeZero.pos L
    have h_tail : pathHolonomy U₂
        (List.ofFn fun k : Fin (L - 1) =>
          (((⟨k.val + 1, by omega⟩, 0, 0), 0), true)) = 1 := by
      have h_gen : ∀ (γ : List ((cubicTorus3 L).Link × Bool)),
          (∀ p ∈ γ, p.2 = true ∧ p.1 ≠ e₀) → pathHolonomy U₂ γ = 1 := by
        intro γ hγ
        induction γ with
        | nil => rfl
        | cons hd tl ih =>
          rcases hd with ⟨e, b⟩
          have hhd := hγ (e, b) (by simp)
          rcases hhd with ⟨hb, hne⟩
          subst hb
          simp [pathHolonomy, U₂, if_neg hne, ih (fun p hp => hγ p (by simp [hp]))]
      refine h_gen _ (fun p hp => ?_)
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨k, rfl⟩
      refine ⟨rfl, fun heq => ?_⟩
      have hv := congrArg (fun x : (cubicTorus3 L).Link => x.1.1.val) heq
      change k.val + 1 = (0 : Fin L).val at hv
      simp at hv
    have h_split : polyakovLoop3 L =
        (e₀, true) :: List.ofFn (fun k : Fin (L - 1) =>
          (((⟨k.val + 1, by omega⟩, 0, 0), 0), true)) := by
      let f : ℕ → (cubicTorus3 L).Link × Bool := fun m =>
        if hm : m < L then (((⟨m, hm⟩, 0, 0), 0), true) else (e₀, true)
      have h_ofFn1 : polyakovLoop3 L = List.ofFn (fun k : Fin L => f k.val) := by
        dsimp [polyakovLoop3]; congr 1; funext k; simp [f, k.isLt]
      have h_ofFn2 : List.ofFn (fun k : Fin (L - 1) =>
          (((⟨k.val + 1, by omega⟩, 0, 0), 0), true)) =
          List.ofFn (fun k : Fin (L - 1) => f (k.val + 1)) := by
        congr 1; funext k; simp [f, (by omega : k.val + 1 < L)]
      rw [h_ofFn1, h_ofFn2]
      have h_succ : ∀ m (hm : m + 1 = L),
          List.ofFn (fun k : Fin L => f k.val) =
            f 0 :: List.ofFn (fun k : Fin m => f (k.val + 1)) := by
        intro m hm
        subst hm
        rw [List.ofFn_succ]
        simp only [Fin.val_zero, Fin.val_succ]
      have h0 : f 0 = (e₀, true) := by
        simp [f, hL, e₀]
      rw [h_succ (L - 1) (Nat.sub_add_cancel hL), h0]
    rw [h_split, pathHolonomy, h_tail, mul_one]
    simp [U₂]
  refine ⟨?_, ?_⟩
  · unfold polyakovObs3; rw [h1, su_one_trace_re]
  · unfold polyakovObs3; rw [h2, suFlip2_trace_re N hN]

/-- Euclidean spatial translation of a `PosTimeConfig` by `a : Fin 3 → ℝ`. -/
def posSpaceShiftConfig (a : Fin 3 → ℝ) (x : PosTimeConfig) : PosTimeConfig where
  n_pts := x.n_pts
  pts   := fun k i => match i with
    | 0 => x.pts k 0
    | 1 => x.pts k 1 + a 0
    | 2 => x.pts k 2 + a 1
    | 3 => x.pts k 3 + a 2
  pos_t := x.pos_t

/-- Pre-Hilbert spatial translation linear operator on `OSPosTestSpace`. -/
noncomputable def osSpaceShiftPre (a : Fin 3 → ℝ) :
    OSPosTestSpace →ₗ[ℂ] OSPosTestSpace where
  toFun := Finsupp.mapDomain (posSpaceShiftConfig a)
  map_add' := fun _ _ => Finsupp.mapDomain_add
  map_smul' := fun c f => Finsupp.mapDomain_smul c f

theorem osSpaceShiftPre_zero (f : OSPosTestSpace) :
    osSpaceShiftPre 0 f = f := by
  have hid : posSpaceShiftConfig 0 = id := by
    funext ⟨n, pts, hpt⟩
    dsimp [posSpaceShiftConfig]
    congr 1
    funext k i
    fin_cases i <;> simp
  change Finsupp.mapDomain (posSpaceShiftConfig 0) f = f
  rw [hid, Finsupp.mapDomain_id]

theorem osSpaceShiftPre_add (a b : Fin 3 → ℝ) (f : OSPosTestSpace) :
    osSpaceShiftPre (a + b) f = osSpaceShiftPre a (osSpaceShiftPre b f) := by
  have hcomp : posSpaceShiftConfig (a + b) =
      (posSpaceShiftConfig a) ∘ (posSpaceShiftConfig b) := by
    funext ⟨n, pts, hpt⟩
    dsimp [posSpaceShiftConfig, Function.comp_def]
    congr 1
    funext k i
    fin_cases i <;> ring
  change Finsupp.mapDomain (posSpaceShiftConfig (a + b)) f =
    Finsupp.mapDomain (posSpaceShiftConfig a) (Finsupp.mapDomain (posSpaceShiftConfig b) f)
  rw [hcomp, Finsupp.mapDomain_comp]

theorem osSpaceShiftPre_unitary {Δ : ℝ} (os : OS4DContinuumTheory Δ)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (a : Fin 3 → ℝ) (f g : OSPosTestSpace) :
    (osConfigForm os h_herm).B (osSpaceShiftPre a f) (osSpaceShiftPre a g) =
      (osConfigForm os h_herm).B f g := by
  let a4 : Space4 := ![0, a 0, a 1, a 2]
  have h_kern : ∀ x y : PosTimeConfig,
      osConfigKernel os (posSpaceShiftConfig a x) (posSpaceShiftConfig a y) =
        osConfigKernel os x y := by
    intro x y
    dsimp [osConfigKernel]
    have happ : Fin.append (fun k => euclidTimeReflect ((posSpaceShiftConfig a x).pts k))
          (posSpaceShiftConfig a y).pts =
        fun k => (Fin.append (fun j => euclidTimeReflect (x.pts j)) y.pts k) + a4 := by
      funext k
      induction k using Fin.addCases with
      | left j =>
        funext i
        fin_cases i <;> simp [Fin.append_left, euclidTimeReflect, posSpaceShiftConfig, a4]
      | right j =>
        funext i
        fin_cases i <;> simp [Fin.append_right, posSpaceShiftConfig, a4]
    change os.os.Schwinger (x.n_pts + y.n_pts)
        (Fin.append (fun k => euclidTimeReflect ((posSpaceShiftConfig a x).pts k))
          (posSpaceShiftConfig a y).pts) =
      os.os.Schwinger (x.n_pts + y.n_pts)
        (Fin.append (fun k => euclidTimeReflect (x.pts k)) y.pts)
    exact (congrArg (os.os.Schwinger (x.n_pts + y.n_pts)) happ).trans (h_trans _ a4 _)
  let F := osConfigForm os h_herm
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero]
    change osConfigInner os 0 (osSpaceShiftPre a g) = osConfigInner os 0 g
    rw [osConfigInner_zero_left, osConfigInner_zero_left]
  · intro f₁ f₂ ih₁ ih₂
    rw [map_add]
    change F.B (osSpaceShiftPre a f₁ + osSpaceShiftPre a f₂) (osSpaceShiftPre a g) =
      F.B (f₁ + f₂) g
    rw [F.add_left, F.add_left, ih₁, ih₂]
  · intro x c
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · rw [map_zero]
      change osConfigInner os _ 0 = osConfigInner os _ 0
      rw [osConfigInner_zero_right, osConfigInner_zero_right]
    · intro g₁ g₂ ih₁ ih₂
      rw [map_add]
      change F.B (osSpaceShiftPre a (Finsupp.single x c))
          (osSpaceShiftPre a g₁ + osSpaceShiftPre a g₂) =
        F.B (Finsupp.single x c) (g₁ + g₂)
      rw [F.add_right, F.add_right, ih₁, ih₂]
    · intro y d
      have hx : Finsupp.single x c = c • osConfigSingle x := by
        dsimp [osConfigSingle]; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hy : Finsupp.single y d = d • osConfigSingle y := by
        dsimp [osConfigSingle]; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hsx : osSpaceShiftPre a (c • osConfigSingle x) =
          c • osConfigSingle (posSpaceShiftConfig a x) := by
        rw [map_smul]; congr 1; exact Finsupp.mapDomain_single
      have hsy : osSpaceShiftPre a (d • osConfigSingle y) =
          d • osConfigSingle (posSpaceShiftConfig a y) := by
        rw [map_smul]; congr 1; exact Finsupp.mapDomain_single
      change F.B (osSpaceShiftPre a (Finsupp.single x c))
          (osSpaceShiftPre a (Finsupp.single y d)) =
        F.B (Finsupp.single x c) (Finsupp.single y d)
      rw [hx, hy, hsx, hsy, F.smul_left, F.smul_right, F.smul_left, F.smul_right]
      change starRingEnd ℂ c * (d * osConfigInner os (osConfigSingle (posSpaceShiftConfig a x))
            (osConfigSingle (posSpaceShiftConfig a y))) =
        starRingEnd ℂ c * (d * osConfigInner os (osConfigSingle x) (osConfigSingle y))
      rw [osConfigInner_single, osConfigInner_single, h_kern x y]

/-- Lifted unitary spatial translation representation `U_space : (Fin 3 → ℝ) → (OSHilbertSpace F →L[ℂ] OSHilbertSpace F)`. -/
noncomputable def osSpaceTransOp {Δ : ℝ} (os : OS4DContinuumTheory Δ)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (a : Fin 3 → ℝ) :
    OSHilbertSpace (osConfigForm os h_herm) →L[ℂ]
      OSHilbertSpace (osConfigForm os h_herm) :=
  osLiftOperator (osConfigForm os h_herm) (osSpaceShiftPre a) 1 zero_le_one (fun x => by
    rw [one_pow, one_mul, osSpaceShiftPre_unitary os h_herm h_trans a x x])

theorem osSpaceTransOp_comm_time {Δ : ℝ} (os : OS4DContinuumTheory Δ)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (M_bd : ℝ) (hM_nn : 0 ≤ M_bd)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M_bd ^ n)
    (a : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    let F := osConfigForm os h_herm
    let T_E := osLiftSemigroup F osTimeShiftSemigroup
      (osTimeShiftSemigroup_contr os h_herm h_kern M_bd hM_nn h_bd)
    (osSpaceTransOp os h_herm h_trans a).comp (T_E t) =
      (T_E t).comp (osSpaceTransOp os h_herm h_trans a) := by
  intro F T_E
  ext1 z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      ((osSpaceTransOp os h_herm h_trans a).comp (T_E t)).continuous
      ((T_E t).comp (osSpaceTransOp os h_herm h_trans a)).continuous
  · intro u
    refine Quotient.inductionOn u fun f => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    dsimp [T_E, osLiftSemigroup, osSpaceTransOp]
    rw [dif_pos ht]
    change osLiftOperator F (osSpaceShiftPre a) 1 zero_le_one _
        (osLiftOperator F (osTimeShiftSemigroup t) 1 zero_le_one _
          (osCompletionMap F (osPreMk F f))) =
      osLiftOperator F (osTimeShiftSemigroup t) 1 zero_le_one _
        (osLiftOperator F (osSpaceShiftPre a) 1 zero_le_one _
          (osCompletionMap F (osPreMk F f)))
    rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe]
    congr 2
    dsimp [osTimeShiftSemigroup]
    rw [dif_pos ht]
    have h_comm_cfg : ∀ x : PosTimeConfig,
        posSpaceShiftConfig a (posTimeShiftConfig t ht x) =
          posTimeShiftConfig t ht (posSpaceShiftConfig a x) := by
      intro x
      dsimp [posSpaceShiftConfig, posTimeShiftConfig]
      congr 1
      funext k i
      fin_cases i <;> rfl
    change Finsupp.mapDomain (posSpaceShiftConfig a) (Finsupp.mapDomain (posTimeShiftConfig t ht) f) =
      Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.mapDomain (posSpaceShiftConfig a) f)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    exact funext h_comm_cfg

end Wilson4DFeynmanKacAndSpatialTrans

/-! ## §42.  4D Feynman–Kac measure equivalence & exact slice transfer representation -/

section Wilson4DFeynmanKacTheorem

theorem exp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Real.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Real.exp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Real.exp_add, ih]

theorem prod_mul_distrib_local {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∏ i ∈ s, f i * g i = (∏ i ∈ s, f i) * ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih]
    ring

def finPredLtEquiv (m : ℕ) : { i : Fin (m + 1) // i.val < m } ≃ Fin m where
  toFun i := ⟨i.1.val, i.2⟩
  invFun j := ⟨⟨j.val, by omega⟩, j.isLt⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

def finPredLastEquiv (m : ℕ) : { i : Fin (m + 1) // ¬ (i.val < m) } ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨m, Nat.lt_succ_self m⟩, by simp⟩
  left_inv := fun ⟨⟨k, hk1⟩, hk2⟩ => by
    apply Subtype.ext; apply Fin.ext
    simp only [Fin.val_mk] at hk2 ⊢
    omega
  right_inv := fun () => rfl

def finSuccEquiv {α : Type*} [MeasurableSpace α] (m : ℕ) :
    (Fin (m + 1) → α) ≃ᵐ ({ i : Fin (m + 1) // i.val < m } → α) ×
      ({ i : Fin (m + 1) // ¬ (i.val < m) } → α) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (m + 1) => α) (fun i => i.val < m)

def finHeadEquiv {α : Type*} [MeasurableSpace α] (m : ℕ) :
    (Fin (m + 1) → α) ≃ᵐ ({ i : Fin (m + 1) // i.val = 0 } → α) ×
      ({ i : Fin (m + 1) // i.val ≠ 0 } → α) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin (m + 1) => α) (fun i => i.val = 0)

def finPredZeroEquiv (m : ℕ) : { i : Fin (m + 1) // i.val = 0 } ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, rfl⟩
  left_inv := fun ⟨⟨k, _⟩, hk⟩ => by apply Subtype.ext; apply Fin.ext; exact hk.symm
  right_inv := fun () => rfl

def finPredPosEquiv (m : ℕ) : { i : Fin (m + 1) // i.val ≠ 0 } ≃ Fin m where
  toFun i := ⟨i.1.val - 1, by have := i.1.isLt; have := i.2; omega⟩
  invFun j := ⟨⟨j.val + 1, by have := j.isLt; omega⟩, by simp⟩
  left_inv := fun ⟨⟨k, hk1⟩, hk2⟩ => by
    apply Subtype.ext; apply Fin.ext
    simp only [Fin.val_mk] at hk2 ⊢
    omega
  right_inv := fun ⟨k, hk⟩ => by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

theorem pi_reindex_mp {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (e : ι₁ ≃ ι₂) :
    let eqv : (ι₂ → α) ≃ᵐ (ι₁ → α) :=
      { toFun := fun f i => f (e i)
        invFun := fun g j => g (e.symm j)
        left_inv := fun f => by funext j; simp
        right_inv := fun g => by funext i; simp
        measurable_toFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
        measurable_invFun := measurable_pi_iff.mpr fun j => measurable_pi_apply (e.symm j) }
    MeasureTheory.MeasurePreserving eqv
      (MeasureTheory.Measure.pi fun _ => μ) (MeasureTheory.Measure.pi fun _ => μ) := by
  intro eqv
  refine ⟨eqv.measurable, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply eqv.measurable (MeasurableSet.univ_pi hs)]
  have hpre : eqv ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun j => s (e.symm j)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqv, Equiv.coe_fn_mk]
    constructor
    · intro h j; simpa using h (e.symm j)
    · intro h i; simpa using h (e i)
  rw [hpre, MeasureTheory.Measure.pi_pi]
  exact Fintype.prod_equiv e.symm (fun j => μ (s (e.symm j))) (fun i => μ (s i)) (fun _ => rfl)

theorem pi_unit_mp {ι : Type*} [Unique ι]
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ] :
    let eqv : (ι → α) ≃ᵐ α :=
      { toFun := fun f => f default
        invFun := fun a _ => a
        left_inv := fun f => by funext i; rw [Unique.eq_default i]
        right_inv := fun _ => rfl
        measurable_toFun := measurable_pi_apply default
        measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id }
    MeasureTheory.MeasurePreserving eqv (MeasureTheory.Measure.pi fun _ => μ) μ := by
  intro eqv
  refine ⟨eqv.measurable, ?_⟩
  ext s hs
  rw [MeasureTheory.Measure.map_apply eqv.measurable hs]
  have hpre : eqv ⁻¹' s = Set.pi Set.univ (fun _ : ι => s) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqv, Equiv.coe_fn_mk]
    exact ⟨fun h i => (Unique.eq_default i).symm ▸ h, fun h => h default⟩
  rw [hpre, MeasureTheory.Measure.pi_pi]
  simp [Finset.prod_const]

/-- Product-measure factorization of finite products of independent bounded observables on `Fin m → α`. -/
theorem integral_pi_fin_prod {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (F : Fin m → α → ℝ)
    (hF_meas : ∀ i, Measurable (F i))
    (M : ℝ) (hM : 0 ≤ M) (hF_bd : ∀ i x, |F i x| ≤ M) :
    ∫ f : Fin m → α, (∏ i : Fin m, F i (f i)) ∂(MeasureTheory.Measure.pi fun _ => μ) =
      ∏ i : Fin m, ∫ x : α, F i x ∂μ := by
  induction m with
  | zero =>
    simp [Measure.real, MeasureTheory.measure_univ]
  | succ m ih =>
    let eqv1 := finSuccEquiv (α := α) m
    have mp1 := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin (m + 1) => μ) (fun i => i.val < m)
    let e_lt := finPredLtEquiv m
    haveI : Unique { i : Fin (m + 1) // ¬ (i.val < m) } :=
      ⟨⟨⟨⟨m, Nat.lt_succ_self m⟩, by simp⟩⟩, fun ⟨⟨k, hk1⟩, hk2⟩ => by
        apply Subtype.ext; apply Fin.ext
        simp only [Fin.val_mk] at hk2 ⊢
        omega⟩
    let eqv_lt : ({ i : Fin (m + 1) // i.val < m } → α) ≃ᵐ (Fin m → α) :=
      { toFun := fun f j => f (e_lt.symm j)
        invFun := fun g i => g (e_lt i)
        left_inv := fun f => by funext i; simp
        right_inv := fun g => by funext j; simp
        measurable_toFun := measurable_pi_iff.mpr fun j => measurable_pi_apply (e_lt.symm j)
        measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (e_lt i) }
    let eqv_last : ({ i : Fin (m + 1) // ¬ (i.val < m) } → α) ≃ᵐ α :=
      { toFun := fun f => f default
        invFun := fun a _ => a
        left_inv := fun f => by funext i; rw [Unique.eq_default i]
        right_inv := fun _ => rfl
        measurable_toFun := measurable_pi_apply default
        measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id }
    let G_prod : (Fin m → α) × α → ℝ := fun p =>
      (∏ j : Fin m, F (e_lt.symm j).1 (p.1 j)) * F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 p.2
    have h_fn_eq : ∀ f : Fin (m + 1) → α,
        (∏ i : Fin (m + 1), F i (f i)) =
          G_prod (eqv_lt (eqv1 f).1, eqv_last (eqv1 f).2) := by
      intro f
      have h_split := Fin.prod_univ_castSucc (fun i : Fin (m + 1) => F i (f i))
      rw [h_split]
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j _ => ?_) ?_
      · dsimp [eqv_lt, e_lt, finPredLtEquiv]; rfl
      · have h_last_eq : (Fin.last m) = (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 := by
          apply Fin.ext
          have hd := (default : { i : Fin (m + 1) // ¬ (i.val < m) }).2
          have hlt := (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1.isLt
          simp only [Fin.val_last, Fin.val_mk]
          omega
        rw [h_last_eq]
        rfl
    let μ_pi_m := MeasureTheory.Measure.pi (fun _ : Fin m => μ)
    haveI : MeasureTheory.IsProbabilityMeasure μ_pi_m := by dsimp [μ_pi_m]; infer_instance
    rw [← (mp1.symm).integral_comp' (fun f => ∏ i : Fin (m + 1), F i (f i))]
    have h_int_sub : MeasureTheory.Integrable
        (fun q : ({ i : Fin (m + 1) // i.val < m } → α) ×
            ({ i : Fin (m + 1) // ¬ (i.val < m) } → α) =>
          (∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt q.1 j)) *
            F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 (eqv_last q.2))
        ((MeasureTheory.Measure.pi fun _ => μ).prod (MeasureTheory.Measure.pi fun _ => μ)) := by
      have hm1 : Measurable (fun q : ({ i : Fin (m + 1) // i.val < m } → α) ×
            ({ i : Fin (m + 1) // ¬ (i.val < m) } → α) =>
          ∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt q.1 j)) :=
        Finset.measurable_prod Finset.univ fun j _ =>
          (hF_meas _).comp ((measurable_pi_apply j).comp (eqv_lt.measurable.comp measurable_fst))
      have hm2 : Measurable (fun q : ({ i : Fin (m + 1) // i.val < m } → α) ×
            ({ i : Fin (m + 1) // ¬ (i.val < m) } → α) =>
          F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 (eqv_last q.2)) :=
        (hF_meas _).comp (eqv_last.measurable.comp measurable_snd)
      refine (MeasureTheory.integrable_const (M ^ (m + 1))).mono'
        (hm1.mul hm2).stronglyMeasurable.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun q => ?_
      rw [Real.norm_eq_abs, abs_mul, pow_succ]
      have hb1 : |∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt q.1 j)| ≤ M ^ m := by
        rw [Finset.abs_prod]
        calc ∏ j : Fin m, |F (e_lt.symm j).1 (eqv_lt q.1 j)|
            ≤ ∏ _j : Fin m, M := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hF_bd _ _)
          _ = M ^ m := by simp [Finset.prod_const]
      exact mul_le_mul hb1 (hF_bd _ _) (abs_nonneg _) (pow_nonneg hM m)
    have h_rew_int :
        (∫ q : ({ i : Fin (m + 1) // i.val < m } → α) ×
            ({ i : Fin (m + 1) // ¬ (i.val < m) } → α),
          ∏ i : Fin (m + 1), F i ((MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : Fin (m + 1) => α) (fun i => i.val < m)).symm q i)
          ∂((MeasureTheory.Measure.pi fun _ => μ).prod (MeasureTheory.Measure.pi fun _ => μ))) =
        ∫ q, (∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt q.1 j)) *
          F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 (eqv_last q.2)
          ∂((MeasureTheory.Measure.pi fun _ => μ).prod (MeasureTheory.Measure.pi fun _ => μ)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => by
        simpa [eqv1, G_prod] using h_fn_eq (eqv1.symm q))
    rw [h_rew_int, MeasureTheory.integral_prod _ h_int_sub]
    have h_in_last : ∀ f_sub : { i : Fin (m + 1) // i.val < m } → α,
        ∫ q2 : { i : Fin (m + 1) // ¬ (i.val < m) } → α,
            (∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt f_sub j)) *
              F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 (eqv_last q2)
          ∂(MeasureTheory.Measure.pi fun _ => μ) =
        (∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt f_sub j)) *
          ∫ x : α, F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 x ∂μ := by
      intro f_sub
      rw [MeasureTheory.integral_const_mul]
      congr 1
      change (∫ q2 : { i : Fin (m + 1) // ¬ (i.val < m) } → α,
          F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 (q2 default)
        ∂(MeasureTheory.Measure.pi fun _ : { i : Fin (m + 1) // ¬ (i.val < m) } => μ)) =
          ∫ x : α, F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 x ∂μ
      have mp_last_local : MeasureTheory.MeasurePreserving eqv_last
          (MeasureTheory.Measure.pi fun _ : { i : Fin (m + 1) // ¬ (i.val < m) } => μ) μ := by
        refine ⟨eqv_last.measurable, ?_⟩
        ext s hs
        rw [MeasureTheory.Measure.map_apply eqv_last.measurable hs]
        have hpre : eqv_last ⁻¹' s =
            Set.pi Set.univ (fun _ : { i : Fin (m + 1) // ¬ (i.val < m) } => s) := by
          ext f
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqv_last,
            Equiv.coe_fn_mk]
          exact ⟨fun h i => (Unique.eq_default i).symm ▸ h, fun h => h default⟩
        rw [hpre, MeasureTheory.Measure.pi_pi]
        simp [Finset.prod_const]
      exact mp_last_local.integral_comp'
        (fun x => F (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 x)
    simp_rw [h_in_last, MeasureTheory.integral_mul_const]
    have mp_l := pi_reindex_mp μ e_lt.symm
    have h_lhs_m :
        (∫ f_sub : { i : Fin (m + 1) // i.val < m } → α,
            (∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt f_sub j))
          ∂(MeasureTheory.Measure.pi fun _ => μ)) =
        ∫ g : Fin m → α, (∏ j : Fin m, F (e_lt.symm j).1 (g j)) ∂μ_pi_m := by
      have h_eq : (fun f_sub => ∏ j : Fin m, F (e_lt.symm j).1 (eqv_lt f_sub j)) =
          fun f_sub => (fun g : Fin m → α => ∏ j : Fin m, F (e_lt.symm j).1 (g j))
            (fun j => f_sub (e_lt.symm j)) := funext fun _ => rfl
      rw [h_eq]
      exact mp_l.integral_comp' (fun g : Fin m → α => ∏ j : Fin m, F (e_lt.symm j).1 (g j))
    rw [h_lhs_m, ih (fun j => F (e_lt.symm j).1) (fun j => hF_meas _) (fun j x => hF_bd _ x),
      Fin.prod_univ_castSucc]
    have h_last_eq : (Fin.last m) = (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1 := by
      apply Fin.ext
      have hd := (default : { i : Fin (m + 1) // ¬ (i.val < m) }).2
      have hlt := (default : { i : Fin (m + 1) // ¬ (i.val < m) }).1.isLt
      simp only [Fin.val_last, Fin.val_mk]
      omega
    have h_cast_eq : ∀ j : Fin m, (e_lt.symm j).1 = j.castSucc := fun j => Fin.ext rfl
    rw [h_last_eq]
    simp_rw [h_cast_eq]

private theorem integral_pi_fin_head {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (F : (Fin (m + 1) → α) → ℂ)
    (hF_meas : Measurable F) (C : ℝ) (hF_bd : ∀ f, ‖F f‖ ≤ C) :
    ∫ f : Fin (m + 1) → α, F f ∂(MeasureTheory.Measure.pi fun _ => μ) =
      ∫ x₀ : α, ∫ f' : Fin m → α, F (Fin.cons x₀ f')
        ∂(MeasureTheory.Measure.pi fun _ => μ) ∂μ := by
  let eqv := finHeadEquiv (α := α) m
  have mp := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin (m + 1) => μ) (fun i => i.val = 0)
  let ep := finPredPosEquiv m
  haveI : Unique { i : Fin (m + 1) // i.val = 0 } :=
    ⟨⟨⟨0, rfl⟩⟩, fun ⟨⟨k, _⟩, hk⟩ => by
      apply Subtype.ext; apply Fin.ext
      simp only [Fin.val_mk, Fin.val_zero] at hk ⊢
      exact hk⟩
  let eqv0 : ({ i : Fin (m + 1) // i.val = 0 } → α) ≃ᵐ α :=
    { toFun := fun f => f default
      invFun := fun a _ => a
      left_inv := fun f => by funext i; rw [Unique.eq_default i]
      right_inv := fun _ => rfl
      measurable_toFun := measurable_pi_apply default
      measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id }
  let eqvp : ({ i : Fin (m + 1) // i.val ≠ 0 } → α) ≃ᵐ (Fin m → α) :=
    { toFun := fun f j => f (ep.symm j)
      invFun := fun g i => g (ep i)
      left_inv := fun f => by funext i; simp
      right_inv := fun g => by funext j; simp
      measurable_toFun := measurable_pi_iff.mpr fun j => measurable_pi_apply (ep.symm j)
      measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (ep i) }
  let μ_0 := MeasureTheory.Measure.pi (fun _ : { i : Fin (m + 1) // i.val = 0 } => μ)
  let μ_p := MeasureTheory.Measure.pi (fun _ : { i : Fin (m + 1) // i.val ≠ 0 } => μ)
  haveI : MeasureTheory.IsProbabilityMeasure μ_0 := by dsimp [μ_0]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_p := by dsimp [μ_p]; infer_instance
  have mp_0 := pi_unit_mp (ι := { i : Fin (m + 1) // i.val = 0 }) μ
  have mp_p := pi_reindex_mp μ ep.symm
  have h_eqv_cons : ∀ q1 q2, eqv.symm (q1, q2) = Fin.cons (eqv0 q1) (eqvp q2) := by
    intro q1 q2
    funext i
    refine Fin.cases ?_ ?_ i
    · have hz : (0 : Fin (m + 1)).val = 0 := rfl
      simp only [eqv, finHeadEquiv, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
        hz, ↓reduceDIte, Fin.cons_zero]
      dsimp [eqv0]
      congr 1
      exact Subsingleton.elim _ _
    · intro j
      have hne : j.succ.val ≠ 0 := by simp [Fin.val_succ]
      simp only [eqv, finHeadEquiv, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
        hne, ↓reduceDIte, Fin.cons_succ]
      dsimp [eqvp]
      rfl
  rw [← (mp.symm).integral_comp']
  have h_int : MeasureTheory.Integrable
      (fun q : ({ i : Fin (m + 1) // i.val = 0 } → α) ×
          ({ i : Fin (m + 1) // i.val ≠ 0 } → α) => F (eqv.symm q)) (μ_0.prod μ_p) := by
    refine (MeasureTheory.integrable_const C).mono'
      (hF_meas.comp eqv.symm.measurable).stronglyMeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun q => hF_bd _
  change (∫ q, F (eqv.symm q) ∂(μ_0.prod μ_p)) = _
  rw [MeasureTheory.integral_prod (fun q => F (eqv.symm q)) h_int]
  have h_inner : ∀ q1 : { i : Fin (m + 1) // i.val = 0 } → α,
      (∫ q2 : { i : Fin (m + 1) // i.val ≠ 0 } → α, F (eqv.symm (q1, q2)) ∂μ_p) =
        ∫ f' : Fin m → α, F (Fin.cons (eqv0 q1) f') ∂(MeasureTheory.Measure.pi fun _ => μ) := by
    intro q1
    simp_rw [h_eqv_cons q1]
    have h_comp : (fun q2 : { i : Fin (m + 1) // i.val ≠ 0 } → α => F (Fin.cons (eqv0 q1) (eqvp q2))) =
        fun q2 => (fun f' : Fin m → α => F (Fin.cons (eqv0 q1) f'))
          (fun j => q2 (ep.symm j)) := funext fun _ => rfl
    rw [h_comp]
    exact mp_p.integral_comp' (fun f' : Fin m → α => F (Fin.cons (eqv0 q1) f'))
  simp_rw [h_inner]
  have h_mp0 : MeasureTheory.MeasurePreserving eqv0 μ_0 μ := by
    refine ⟨eqv0.measurable, ?_⟩
    ext s hs
    rw [MeasureTheory.Measure.map_apply eqv0.measurable hs]
    have hpre : eqv0 ⁻¹' s = Set.pi Set.univ (fun _ => s) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqv0,
        MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      exact ⟨fun h i => (Unique.eq_default i).symm ▸ h, fun h => h default⟩
    rw [hpre, MeasureTheory.Measure.pi_pi]
    simp [Finset.prod_const]
  exact h_mp0.integral_comp' (fun y : α =>
    ∫ f' : Fin m → α, F (Fin.cons y f') ∂(MeasureTheory.Measure.pi fun _ => μ))

/-- `slice4DFieldEquiv` promoted to a `MeasurableEquiv`. -/
def slice4DFieldMeasEquiv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      (Fin Lt → GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (Fin Lt → GaugeGrp3 Ls N) where
  toEquiv := slice4DFieldEquiv Ls Lt N
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_iff.mpr fun t => measurable_pi_iff.mpr fun ⟨y, d⟩ => ?_
      fin_cases d
      · exact measurable_pi_apply ((t, y.1, y.2.1, y.2.2), 1)
      · exact measurable_pi_apply ((t, y.1, y.2.1, y.2.2), 2)
      · exact measurable_pi_apply ((t, y.1, y.2.1, y.2.2), 3)
    · refine measurable_pi_iff.mpr fun t => measurable_pi_iff.mpr fun y => ?_
      exact measurable_pi_apply ((t, y.1, y.2.1, y.2.2), 0)
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    fin_cases d
    · exact (measurable_pi_apply (a, b, c)).comp ((measurable_pi_apply t).comp measurable_snd)
    · exact (measurable_pi_apply ((a, b, c), 0)).comp ((measurable_pi_apply t).comp measurable_fst)
    · exact (measurable_pi_apply ((a, b, c), 1)).comp ((measurable_pi_apply t).comp measurable_fst)
    · exact (measurable_pi_apply ((a, b, c), 2)).comp ((measurable_pi_apply t).comp measurable_fst)

/-- Exact measure-preserving factorization of `spacetimeHaarMeasure` across time slices. -/
theorem spacetimeHaarMeasure_slice_mp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MeasurePreserving (slice4DFieldMeasEquiv Ls Lt N)
      (spacetimeHaarMeasure Ls Lt N)
      ((MeasureTheory.Measure.pi fun _ : Fin Lt => latticeHaarMeasure Ls N).prod
        (MeasureTheory.Measure.pi fun _ : Fin Lt => gaugeGrpHaarMeasure Ls N)) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let μ_4 := spacetimeHaarMeasure Ls Lt N
  let μ_3 := latticeHaarMeasure Ls N
  let μ_g := gaugeGrpHaarMeasure Ls N
  let μ_sl := MeasureTheory.Measure.pi fun _ : Fin Lt => μ_3
  let μ_tm := MeasureTheory.Measure.pi fun _ : Fin Lt => μ_g
  let μ_prod := μ_sl.prod μ_tm
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob Ls N
  haveI := gaugeGrpHaarMeasure_prob Ls N
  haveI : MeasureTheory.IsProbabilityMeasure μ_sl := by dsimp [μ_sl]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_tm := by dsimp [μ_tm]; infer_instance
  let eqv := slice4DFieldMeasEquiv Ls Lt N
  suffices h_symm : MeasureTheory.MeasurePreserving eqv.symm μ_prod μ_4 from h_symm.symm
  refine ⟨eqv.symm.measurable, ?_⟩
  change MeasureTheory.Measure.map eqv.symm μ_prod = MeasureTheory.Measure.pi fun _ => suHaar N
  symm
  refine MeasureTheory.Measure.pi_eq fun r hr => ?_
  erw [MeasureTheory.Measure.map_apply eqv.symm.measurable (MeasurableSet.univ_pi hr)]
  let S_sp : Set (Fin Lt → GaugeField (cubicTorus3 Ls) G) :=
    Set.pi Set.univ fun t => Set.pi Set.univ fun e =>
      match e.2 with
      | 0 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 1)
      | 1 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 2)
      | 2 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 3)
  let S_tm : Set (Fin Lt → GaugeGrp3 Ls N) :=
    Set.pi Set.univ fun t => Set.pi Set.univ fun x => r ((t, x.1, x.2.1, x.2.2), 0)
  have hpre : eqv.symm ⁻¹' Set.pi Set.univ r = S_sp ×ˢ S_tm := by
    ext ⟨U_sl, g_tm⟩
    have h_lhs : (U_sl, g_tm) ∈ eqv.symm ⁻¹' Set.pi Set.univ r ↔
        ∀ e, (slice4DFieldEquiv Ls Lt N).symm (U_sl, g_tm) e ∈ r e := by
      rw [Set.mem_preimage, Set.mem_pi]
      simp only [Set.mem_univ, true_implies]
      rfl
    have h_rhs : (U_sl, g_tm) ∈ S_sp ×ˢ S_tm ↔ (U_sl ∈ S_sp ∧ g_tm ∈ S_tm) := Set.mem_prod
    rw [h_lhs, h_rhs]
    simp only [S_sp, S_tm, Set.mem_pi, Set.mem_univ, true_implies]
    dsimp only [slice4DFieldEquiv, Equiv.symm]
    constructor
    · intro h
      refine ⟨fun t ⟨x, d⟩ => ?_, fun t x => ?_⟩
      · fin_cases d
        · simpa using h ((t, x.1, x.2.1, x.2.2), 1)
        · simpa using h ((t, x.1, x.2.1, x.2.2), 2)
        · simpa using h ((t, x.1, x.2.1, x.2.2), 3)
      · simpa using h ((t, x.1, x.2.1, x.2.2), 0)
    · rintro ⟨h1, h2⟩ ⟨⟨t, a, b, c⟩, d⟩
      fin_cases d
      · simpa using h2 t (a, b, c)
      · simpa using h1 t ((a, b, c), 0)
      · simpa using h1 t ((a, b, c), 1)
      · simpa using h1 t ((a, b, c), 2)
  rw [hpre, MeasureTheory.Measure.prod_prod]
  have h_sp_val : μ_sl S_sp =
      ∏ t : Fin Lt, ∏ e : (cubicTorus3 Ls).Link,
        suHaar N (match e.2 with
          | 0 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 1)
          | 1 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 2)
          | 2 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 3)) := by
    dsimp [μ_sl, S_sp]
    rw [MeasureTheory.Measure.pi_pi]
    refine Finset.prod_congr rfl fun t _ => ?_
    dsimp [μ_3, latticeHaarMeasure]
    exact MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
  have h_tm_val : μ_tm S_tm =
      ∏ t : Fin Lt, ∏ x : (cubicTorus3 Ls).Site,
        suHaar N (r ((t, x.1, x.2.1, x.2.2), 0)) := by
    dsimp [μ_tm, S_tm]
    rw [MeasureTheory.Measure.pi_pi]
    refine Finset.prod_congr rfl fun t _ => ?_
    dsimp [μ_g, gaugeGrpHaarMeasure]
    exact MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
  rw [h_sp_val, h_tm_val]
  let idxEquiv : (cubicTorus4 Ls Lt).Link ≃
      (Fin Lt × (cubicTorus3 Ls).Link) ⊕ (Fin Lt × (cubicTorus3 Ls).Site) :=
    { toFun := fun ⟨⟨t, a, b, c⟩, d⟩ => match d with
        | 0 => Sum.inr (t, (a, b, c))
        | 1 => Sum.inl (t, ((a, b, c), 0))
        | 2 => Sum.inl (t, ((a, b, c), 1))
        | 3 => Sum.inl (t, ((a, b, c), 2))
      invFun := fun s => match s with
        | Sum.inl (t, ((a, b, c), 0)) => ((t, a, b, c), 1)
        | Sum.inl (t, ((a, b, c), 1)) => ((t, a, b, c), 2)
        | Sum.inl (t, ((a, b, c), 2)) => ((t, a, b, c), 3)
        | Sum.inr (t, (a, b, c)) => ((t, a, b, c), 0)
      left_inv := fun ⟨⟨t, a, b, c⟩, d⟩ => by fin_cases d <;> rfl
      right_inv := fun s => by
        rcases s with ⟨t, ⟨⟨a, b, c⟩, d⟩⟩ | ⟨t, ⟨a, b, c⟩⟩
        · fin_cases d <;> rfl
        · rfl }
  have h_prod_4 := Fintype.prod_equiv idxEquiv
    (fun e => suHaar N (r e))
    (fun s => match s with
      | Sum.inl (t, e) => suHaar N (match e.2 with
          | 0 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 1)
          | 1 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 2)
          | 2 => r ((t, e.1.1, e.1.2.1, e.1.2.2), 3))
      | Sum.inr (t, x) => suHaar N (r ((t, x.1, x.2.1, x.2.2), 0)))
    (fun ⟨⟨t, a, b, c⟩, d⟩ => by fin_cases d <;> rfl)
  rw [h_prod_4, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type]

theorem wilsonAction_cubic3_eq_sum (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    (V : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubicPlaquettes Ls) V =
      β * ∑ y : (cubicTorus3 Ls).Site,
        (wilsonPlaquetteTerm ⟨y, cubicPlaquette y 0 1, cubicPlaquette_isPath y 0 1⟩ V +
         wilsonPlaquetteTerm ⟨y, cubicPlaquette y 0 2, cubicPlaquette_isPath y 0 2⟩ V +
         wilsonPlaquetteTerm ⟨y, cubicPlaquette y 1 2, cubicPlaquette_isPath y 1 2⟩ V) := by
  unfold wilsonAction cubicPlaquettes
  rw [sum_map_flatMap, sum_map_univ_toList]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [List.map_cons, List.sum_cons]
  ring

/-- Exact slice-by-slice factorization of the 4D Wilson Boltzmann weight `cubic4WilsonWeight`. -/
theorem cubic4WilsonWeight_slice_factor (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    let U_sl := (slice4DFieldEquiv Ls Lt N U).1
    let g_tm := (slice4DFieldEquiv Ls Lt N U).2
    cubic4WilsonWeight Ls Lt N β U =
      ∏ t : Fin Lt,
        (cubicWilsonWeight Ls N β (U_sl t) *
         cubicWilsonWeight Ls N β (U_sl (t + 1)) *
         ∏ e : (cubicTorus3 Ls).Link,
           temporalPlaqFactor β e (U_sl t) (U_sl (t + 1)) (g_tm t)) := by
  intro U_sl g_tm
  let siteEquiv : (cubicTorus4 Ls Lt).Site ≃ Fin Lt × (cubicTorus3 Ls).Site :=
    { toFun := fun x => (x.1, (x.2.1, x.2.2.1, x.2.2.2))
      invFun := fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _, _⟩⟩ => rfl }
  have h_sp_match : ∀ (t : Fin Lt) (y : (cubicTorus3 Ls).Site) (d₁ d₂ : Fin 3),
      wilsonPlaquetteTerm
          ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) d₁.succ d₂.succ,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) d₁.succ d₂.succ⟩ U =
        wilsonPlaquetteTerm ⟨y, cubicPlaquette y d₁ d₂, cubicPlaquette_isPath y d₁ d₂⟩ (U_sl t) := by
    intro t ⟨a, b, c⟩ d₁ d₂
    have hsh : ∀ (d : Fin 3) (a' b' c' : Fin Ls),
        cubicShift4 Ls Lt d.succ (t, a', b', c') =
          (t, (cubicShift Ls d (a', b', c')).1,
              (cubicShift Ls d (a', b', c')).2.1,
              (cubicShift Ls d (a', b', c')).2.2) := by
      intro d a' b' c'; fin_cases d <;> rfl
    have hlink : ∀ (a' b' c' : Fin Ls) (d : Fin 3),
        U ((t, a', b', c'), d.succ) = U_sl t ((a', b', c'), d) := by
      intro a' b' c' d; fin_cases d <;> rfl
    unfold wilsonPlaquetteTerm
    simp only [cubic4Plaquette, cubicPlaquette, pathHolonomy, hsh, hlink]
  have h_tm_match : ∀ (t : Fin Lt) (y : (cubicTorus3 Ls).Site) (d : Fin 3),
      Real.exp (-(β * wilsonPlaquetteTerm
          ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 d.succ,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 d.succ⟩ U)) =
        temporalPlaqFactor β (y, d) (U_sl t) (U_sl (t + 1)) (g_tm t) := by
    intro t y d
    have hsh0 : cubicShift4 Ls Lt 0 (t, y.1, y.2.1, y.2.2) = (t + 1, y.1, y.2.1, y.2.2) := rfl
    have hshd : cubicShift4 Ls Lt d.succ (t, y.1, y.2.1, y.2.2) =
        (t, (cubicShift Ls d y).1, (cubicShift Ls d y).2.1, (cubicShift Ls d y).2.2) := by
      rcases y with ⟨a, b, c⟩; fin_cases d <;> rfl
    have hU_0 : ∀ z : (cubicTorus3 Ls).Site,
        U ((t, z.1, z.2.1, z.2.2), 0) = g_tm t z := fun _ => rfl
    have hU_d : ∀ (t' : Fin Lt) (z : (cubicTorus3 Ls).Site),
        U ((t', z.1, z.2.1, z.2.2), d.succ) = U_sl t' (z, d) := by
      intro t' z; fin_cases d <;> rfl
    have h_hol : pathHolonomy U (cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 d.succ) =
        (U_sl t (y, d) * (gaugeAct (g_tm t) (U_sl (t + 1)) (y, d))⁻¹)⁻¹ := by
      simp only [cubic4Plaquette, pathHolonomy, hsh0, hshd, hU_0, hU_d, gaugeAct,
        cubicTorus3, mul_inv_rev, inv_inv, mul_one, mul_assoc]
    unfold wilsonPlaquetteTerm temporalPlaqFactor
    rw [h_hol, su_trace_inv_re]
  have h_sp_sum :
      β * ∑ t : Fin Lt, ∑ y : (cubicTorus3 Ls).Site,
        (wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 2,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 3⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 2 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 2 3⟩ U) =
      ∑ t : Fin Lt, ((1 / 2 : ℝ) * wilsonAction β (cubicPlaquettes Ls) (U_sl t) +
        (1 / 2 : ℝ) * wilsonAction β (cubicPlaquettes Ls) (U_sl (t + 1))) := by
    have h_each : ∀ t : Fin Lt,
        β * ∑ y : (cubicTorus3 Ls).Site,
          (wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
              cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 2,
              cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 2⟩ U +
           wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
              cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 3,
              cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 3⟩ U +
           wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
              cubic4Plaquette (t, y.1, y.2.1, y.2.2) 2 3,
              cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 2 3⟩ U) =
        wilsonAction β (cubicPlaquettes Ls) (U_sl t) := by
      intro t
      rw [wilsonAction_cubic3_eq_sum]
      rfl
    rw [Finset.mul_sum]
    simp_rw [h_each, Finset.sum_add_distrib, ← Finset.mul_sum]
    let e_shift : Fin Lt ≃ Fin Lt :=
      { toFun := fun t => t + 1
        invFun := fun t => t - 1
        left_inv := fun t => by simp [sub_eq_add_neg, add_assoc]
        right_inv := fun t => by simp [sub_eq_add_neg, add_assoc] }
    have h_sh : ∑ t : Fin Lt, wilsonAction β (cubicPlaquettes Ls) (U_sl (t + 1)) =
        ∑ t : Fin Lt, wilsonAction β (cubicPlaquettes Ls) (U_sl t) :=
      Fintype.sum_equiv e_shift _ _ (fun _ => rfl)
    rw [h_sh]
    ring
  unfold cubic4WilsonWeight
  rw [wilsonAction_cubic4_eq_sum, Fintype.sum_equiv siteEquiv _ _ (fun _ => rfl),
    Fintype.sum_prod_type]
  have h_site_split :
      β * ∑ t : Fin Lt, ∑ y : (cubicTorus3 Ls).Site,
        sitePlaqSum4 Ls Lt N U (t, y) =
      (β * ∑ t : Fin Lt, ∑ y : (cubicTorus3 Ls).Site,
        (wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 2,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 1 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 1 3⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 2 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 2 3⟩ U)) +
      (β * ∑ t : Fin Lt, ∑ y : (cubicTorus3 Ls).Site,
        (wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 1,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 1⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 2,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 3⟩ U)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rcases y with ⟨a, b, c⟩
    dsimp [sitePlaqSum4]
    ring
  rw [h_site_split, h_sp_sum, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, exp_finset_sum]
  have h_tm_exp :
      Real.exp (-(β * ∑ t : Fin Lt, ∑ y : (cubicTorus3 Ls).Site,
        (wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 1,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 1⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 2,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, y.1, y.2.1, y.2.2),
            cubic4Plaquette (t, y.1, y.2.1, y.2.2) 0 3,
            cubic4Plaquette_isPath (t, y.1, y.2.1, y.2.2) 0 3⟩ U))) =
      ∏ t : Fin Lt, ∏ e : (cubicTorus3 Ls).Link,
        temporalPlaqFactor β e (U_sl t) (U_sl (t + 1)) (g_tm t) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, exp_finset_sum]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, exp_finset_sum]
    have h_link_prod :
        (∏ e : (cubicTorus3 Ls).Link, temporalPlaqFactor β e (U_sl t) (U_sl (t + 1)) (g_tm t)) =
          ∏ y : (cubicTorus3 Ls).Site,
            (temporalPlaqFactor β (y, 0) (U_sl t) (U_sl (t + 1)) (g_tm t) *
             temporalPlaqFactor β (y, 1) (U_sl t) (U_sl (t + 1)) (g_tm t) *
             temporalPlaqFactor β (y, 2) (U_sl t) (U_sl (t + 1)) (g_tm t)) := by
      change (∏ p : (cubicTorus3 Ls).Site × Fin 3,
          temporalPlaqFactor β p (U_sl t) (U_sl (t + 1)) (g_tm t)) = _
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [Fin.prod_univ_three]
    rw [h_link_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    have hs0 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
    have hs1 : (1 : Fin 3).succ = (2 : Fin 4) := rfl
    have hs2 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
    rw [← h_tm_match t y 0, ← h_tm_match t y 1, ← h_tm_match t y 2, hs0, hs1, hs2,
      ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [h_tm_exp, ← prod_mul_distrib_local]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [neg_add, Real.exp_add]
  congr 1
  unfold cubicWilsonWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Exact 4D slice transfer kernel `K_slice(U, U') = exp(-½(S_W[U] + S_W[U'])) K_4D(U, U')`. -/
noncomputable def wilson4DSliceKernel (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  wilsonKernel β (cubicPlaquettes Ls) (wilson4DKernel Ls N β) U U'

theorem continuous_wilson4DSliceKernel (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous (Function.uncurry (wilson4DSliceKernel Ls N β)) :=
  continuous_cubicWilsonKernel Ls N β (wilson4DKernel Ls N β)
    (continuous_wilson4DKernel Ls N hN β hβ)

theorem wilson4DSliceKernel_bounds (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilson4DSliceKernel Ls N β U U' ∧ wilson4DSliceKernel Ls N β U U' ≤ 1 :=
  wilsonKernel_cubic_le Ls N β hβ (wilson4DKernel Ls N β)
    (fun A B => (Real.exp_pos _).le.trans (wilson4DKernel_bounds Ls N hN β hβ A B).1)
    1 (fun A B => (wilson4DKernel_bounds Ls N hN β hβ A B).2) U U'

private theorem pi_fin_prod_const_helper {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (ν : MeasureTheory.Measure (Fin m → α))
    (hν : ∀ s : Fin m → Set α, (∀ i, MeasurableSet (s i)) →
      ν (Set.pi Set.univ s) = ∏ i, μ (s i))
    (F : Fin m → α → ℝ) (hF_m : ∀ i, Measurable (F i))
    (hF_bd : ∀ i x, |F i x| ≤ 1)
    (G : Fin m → ℝ) (hG : ∀ i, (∫ x, F i x ∂μ) = G i) :
    (∫ f : Fin m → α, ∏ i : Fin m, F i (f i) ∂ν) = ∏ i : Fin m, G i := by
  have hν_eq : ν = MeasureTheory.Measure.pi (fun _ : Fin m => μ) :=
    (MeasureTheory.Measure.pi_eq hν).symm
  rw [hν_eq, integral_pi_fin_prod μ m F hF_m 1 zero_le_one hF_bd]
  exact Finset.prod_congr rfl fun i _ => hG i

private noncomputable def sliceTWeight (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    (A B : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (g : GaugeGrp3 Ls N) : ℝ :=
  cubicWilsonWeight Ls N β A * cubicWilsonWeight Ls N β B *
    ∏ e : (cubicTorus3 Ls).Link, temporalPlaqFactor β e A B g

private theorem measurable_sliceTWeight (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A B : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Measurable (sliceTWeight Ls N β A B) := by
  let U_sl : Fin 2 → GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) := ![A, B]
  let map_g : GaugeGrp3 Ls N →
      GaugeField (cubicTorus4 Ls 2) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun g => (slice4DFieldEquiv Ls 2 N).symm (U_sl, ![g, fun _ => 1])
  have hm_map : Measurable map_g := by
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    fin_cases d
    · fin_cases t
      · change Measurable (fun g : (cubicTorus3 Ls).Site → Matrix.specialUnitaryGroup (Fin N) ℂ =>
          g (a, b, c))
        exact measurable_pi_apply (a, b, c)
      · change Measurable (fun _ : GaugeGrp3 Ls N => (1 : Matrix.specialUnitaryGroup (Fin N) ℂ))
        exact measurable_const
    · change Measurable (fun _ : GaugeGrp3 Ls N => U_sl t ((a, b, c), 0))
      exact measurable_const
    · change Measurable (fun _ : GaugeGrp3 Ls N => U_sl t ((a, b, c), 1))
      exact measurable_const
    · change Measurable (fun _ : GaugeGrp3 Ls N => U_sl t ((a, b, c), 2))
      exact measurable_const
  let c₀ : ℝ := sliceTWeight Ls N β B A (fun _ => 1)
  have hc₀_pos : 0 < c₀ := by
    dsimp [c₀, sliceTWeight]
    refine mul_pos (mul_pos ?_ ?_) ?_
    · unfold cubicWilsonWeight; exact Real.exp_pos _
    · unfold cubicWilsonWeight; exact Real.exp_pos _
    · refine Finset.prod_pos fun e _ => ?_
      unfold temporalPlaqFactor
      exact Real.exp_pos _
  have h_eq_w : ∀ g : GaugeGrp3 Ls N,
      cubic4WilsonWeight Ls 2 N β (map_g g) = sliceTWeight Ls N β A B g * c₀ := by
    intro g
    have hf := cubic4WilsonWeight_slice_factor Ls 2 N β (map_g g)
    have hr : slice4DFieldEquiv Ls 2 N (map_g g) = (U_sl, ![g, fun _ => 1]) :=
      (slice4DFieldEquiv Ls 2 N).apply_symm_apply _
    rw [hr] at hf
    dsimp only at hf
    rw [hf, Fin.prod_univ_two]
    have h0 : U_sl 0 = A := rfl
    have h1 : U_sl 1 = B := rfl
    have h10 : U_sl ((1 : Fin 2) + 1) = A := rfl
    have hg0 : (![g, fun _ : (cubicTorus3 Ls).Site => (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)] :
        Fin 2 → GaugeGrp3 Ls N) 0 = g := rfl
    have hg1 : (![g, fun _ : (cubicTorus3 Ls).Site => (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)] :
        Fin 2 → GaugeGrp3 Ls N) 1 = fun _ => 1 := rfl
    dsimp only [c₀, sliceTWeight]
    rw [h0, h1, h10, hg0, hg1]
    rfl
  have h_fn_eq : sliceTWeight Ls N β A B =
      fun g => c₀⁻¹ * cubic4WilsonWeight Ls 2 N β (map_g g) := by
    funext g
    rw [h_eq_w g, mul_comm (sliceTWeight Ls N β A B g) c₀, ← mul_assoc,
      inv_mul_cancel₀ hc₀_pos.ne', one_mul]
  rw [h_fn_eq]
  exact measurable_const.mul ((measurable_cubic4WilsonWeight Ls 2 N β).comp hm_map)

private theorem abs_sliceTWeight_le_one (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    (A B : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (g : GaugeGrp3 Ls N) :
    |sliceTWeight Ls N β A B g| ≤ 1 := by
  have hw1 := cubicWilsonWeight_bounds Ls N β hβ A
  have hw2 := cubicWilsonWeight_bounds Ls N β hβ B
  have hwn1 : 0 ≤ cubicWilsonWeight Ls N β A := by unfold cubicWilsonWeight; exact (Real.exp_pos _).le
  have hwn2 : 0 ≤ cubicWilsonWeight Ls N β B := by unfold cubicWilsonWeight; exact (Real.exp_pos _).le
  have htp_nn : 0 ≤ ∏ e : (cubicTorus3 Ls).Link, temporalPlaqFactor β e A B g :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have htp_le1 : ∏ e : (cubicTorus3 Ls).Link, temporalPlaqFactor β e A B g ≤ 1 := by
    calc ∏ e : (cubicTorus3 Ls).Link, temporalPlaqFactor β e A B g
        ≤ ∏ _e : (cubicTorus3 Ls).Link, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun e _ => (temporalPlaqFactor_bounds hN β hβ e A B g).2)
      _ = 1 := by simp
  have h_nn : 0 ≤ sliceTWeight Ls N β A B g := mul_nonneg (mul_nonneg hwn1 hwn2) htp_nn
  rw [abs_of_nonneg h_nn]
  calc sliceTWeight Ls N β A B g ≤ (1 * 1) * 1 :=
        mul_le_mul (mul_le_mul hw1.2 hw2.2 hwn2 zero_le_one) htp_le1 htp_nn (by positivity)
    _ = 1 := by ring

private theorem integral_sliceTWeight (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A B : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (∫ g : GaugeGrp3 Ls N, sliceTWeight Ls N β A B g ∂(gaugeGrpHaarMeasure Ls N)) =
      wilson4DSliceKernel Ls N β A B := by
  have h_exp : Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes Ls) A + wilsonAction β (cubicPlaquettes Ls) B)) =
      cubicWilsonWeight Ls N β A * cubicWilsonWeight Ls N β B := by
    unfold cubicWilsonWeight; rw [← Real.exp_add]; congr 1; ring
  have h_ker : wilson4DSliceKernel Ls N β A B =
      (cubicWilsonWeight Ls N β A * cubicWilsonWeight Ls N β B) *
        ∫ g : GaugeGrp3 Ls N, ∏ e : (cubicTorus3 Ls).Link,
          temporalPlaqFactor β e A B g ∂(gaugeGrpHaarMeasure Ls N) := by
    unfold wilson4DSliceKernel wilsonKernel wilson4DKernel
    rw [h_exp]
  rw [h_ker]
  exact MeasureTheory.integral_const_mul _ _

/-- Exact integration over `GaugeGrp3` reducing `cubic4Schwinger` to spatial-slice integrals. -/
theorem cubic4Schwinger_eq_slice_integral (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin Lt →
      (GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ t, Measurable (obs t))
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs) (h_bd : ∀ t V, ‖obs t V‖ ≤ M_obs) :
    let μ_sl := MeasureTheory.Measure.pi fun _ : Fin Lt => latticeHaarMeasure Ls N
    ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) *
      cubic4Schwinger Ls Lt N β Lt (fun t U => obs t ((slice4DFieldEquiv Ls Lt N U).1 t)) =
      ∫ U_sl, (∏ t : Fin Lt, obs t (U_sl t) * ((wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)) : ℝ) : ℂ))
        ∂μ_sl := by
  intro μ_sl
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_L := GaugeField (cubicTorus3 Ls) G
  let μ_4 := spacetimeHaarMeasure Ls Lt N
  let μ_g := gaugeGrpHaarMeasure Ls N
  let μ_tm := MeasureTheory.Measure.pi fun _ : Fin Lt => μ_g
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob Ls N
  haveI := gaugeGrpHaarMeasure_prob Ls N
  haveI : MeasureTheory.IsProbabilityMeasure μ_sl := by dsimp [μ_sl]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_tm := by dsimp [μ_tm]; infer_instance
  have hZ_pos : 0 < cubic4PartitionFn Ls Lt N β := cubic4PartitionFn_pos Ls Lt N β hβ
  have hZ_ne : ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ_pos.ne'
  unfold cubic4Schwinger
  rw [← mul_assoc, mul_inv_cancel₀ hZ_ne, one_mul]
  let eqv := slice4DFieldMeasEquiv Ls Lt N
  have mp := spacetimeHaarMeasure_slice_mp Ls Lt N
  have h_eq_comp :
      (∫ U, (∏ t : Fin Lt, obs t ((slice4DFieldEquiv Ls Lt N U).1 t)) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ_4) =
        ∫ U, (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
          (∏ t : Fin Lt, obs t (p.1 t)) *
            ((cubic4WilsonWeight Ls Lt N β (eqv.symm p) : ℝ) : ℂ)) (eqv U) ∂μ_4 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp only
    rw [eqv.symm_apply_apply U]
    rfl
  have h_mp_int := mp.integral_comp'
    (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
      (∏ t : Fin Lt, obs t (p.1 t)) *
        ((cubic4WilsonWeight Ls Lt N β (eqv.symm p) : ℝ) : ℂ))
  rw [h_eq_comp]
  change (∫ U, (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
      (∏ t : Fin Lt, obs t (p.1 t)) *
        ((cubic4WilsonWeight Ls Lt N β (eqv.symm p) : ℝ) : ℂ))
      (slice4DFieldMeasEquiv Ls Lt N U) ∂(spacetimeHaarMeasure Ls Lt N)) = _
  rw [h_mp_int]
  have h_int_p : MeasureTheory.Integrable
      (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
        (∏ t : Fin Lt, obs t (p.1 t)) *
          ((cubic4WilsonWeight Ls Lt N β (eqv.symm p) : ℝ) : ℂ))
      (μ_sl.prod μ_tm) := by
    have hm_obs : Measurable (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
        ∏ t : Fin Lt, obs t (p.1 t)) :=
      Finset.measurable_prod Finset.univ fun t _ =>
        (h_meas t).comp ((measurable_pi_apply t).comp measurable_fst)
    have hm_w : Measurable (fun p : (Fin Lt → G_L) × (Fin Lt → GaugeGrp3 Ls N) =>
        ((cubic4WilsonWeight Ls Lt N β (eqv.symm p) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((measurable_cubic4WilsonWeight Ls Lt N β).comp eqv.symm.measurable)
    refine (MeasureTheory.integrable_const (M_obs ^ Lt)).mono'
      (hm_obs.mul hm_w).stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    have hwb := cubic4WilsonWeight_bounds Ls Lt N β hβ (eqv.symm p)
    have hwnn : 0 ≤ cubic4WilsonWeight Ls Lt N β (eqv.symm p) := by
      unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn]
    calc ‖∏ t : Fin Lt, obs t (p.1 t)‖ * cubic4WilsonWeight Ls Lt N β (eqv.symm p)
        ≤ M_obs ^ Lt * 1 := mul_le_mul (norm_prod_fin_le _ M_obs hM_obs (fun t => h_bd t _))
            hwb.2 hwnn (pow_nonneg hM_obs Lt)
      _ = M_obs ^ Lt := mul_one _
  rw [MeasureTheory.integral_prod _ h_int_p]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_sl => ?_)
  dsimp only
  have h_w_eq : ∀ g_tm : Fin Lt → GaugeGrp3 Ls N,
      cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) =
        ∏ t : Fin Lt, (cubicWilsonWeight Ls N β (U_sl t) *
          cubicWilsonWeight Ls N β (U_sl (t + 1)) *
          ∏ e : (cubicTorus3 Ls).Link,
            temporalPlaqFactor β e (U_sl t) (U_sl (t + 1)) (g_tm t)) := fun g_tm => by
    have h := cubic4WilsonWeight_slice_factor Ls Lt N β (eqv.symm (U_sl, g_tm))
    simpa [eqv, slice4DFieldMeasEquiv] using h
  have h_pull :
      (∫ g_tm : Fin Lt → GaugeGrp3 Ls N, (∏ t : Fin Lt, obs t (U_sl t)) *
          ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm) =
        (∏ t : Fin Lt, obs t (U_sl t)) *
          ((∫ g_tm : Fin Lt → GaugeGrp3 Ls N,
              cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) ∂μ_tm : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have h_int_c : MeasureTheory.Integrable
        (fun g_tm => ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ)) μ_tm := by
      refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
        ((Complex.continuous_ofReal.measurable.comp ((measurable_cubic4WilsonWeight Ls Lt N β).comp
          (eqv.symm.measurable.comp (measurable_const.prodMk measurable_id)))).stronglyMeasurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun g_tm => ?_)
      have hwb := cubic4WilsonWeight_bounds Ls Lt N β hβ (eqv.symm (U_sl, g_tm))
      have hwnn : 0 ≤ cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) := by
        unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn]; exact hwb.2
    have hre : (∫ g_tm, ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm).re =
        ∫ g_tm, cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) ∂μ_tm := by
      change RCLike.re (∫ g_tm, ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm) = _
      rw [← integral_re h_int_c]; rfl
    have him : (∫ g_tm, ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm).im = 0 := by
      have h1 : (∫ g_tm, ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm).im =
          RCLike.re (-Complex.I * ∫ g_tm, ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_int_c.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun g_tm => ?_)
      simp [Complex.mul_re]
    exact Complex.ext hre him
  change (∫ g_tm : Fin Lt → GaugeGrp3 Ls N, (∏ t : Fin Lt, obs t (U_sl t)) *
      ((cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm)) : ℝ) : ℂ) ∂μ_tm) =
    ∏ t : Fin Lt, obs t (U_sl t) * ((wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)) : ℝ) : ℂ)
  rw [h_pull]
  have h_F_eq :
      (fun g_tm : Fin Lt → GaugeGrp3 Ls N =>
        cubic4WilsonWeight Ls Lt N β (eqv.symm (U_sl, g_tm))) =
      fun g_tm => ∏ t : Fin Lt, sliceTWeight Ls N β (U_sl t) (U_sl (t + 1)) (g_tm t) :=
    funext h_w_eq
  rw [h_F_eq]
  have h_pi_eq :
      (∫ g_tm : Fin Lt → GaugeGrp3 Ls N,
          ∏ t : Fin Lt, sliceTWeight Ls N β (U_sl t) (U_sl (t + 1)) (g_tm t) ∂μ_tm) =
        ∏ t : Fin Lt, wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)) :=
    pi_fin_prod_const_helper μ_g Lt μ_tm
      (fun s _ => MeasureTheory.Measure.pi_pi (fun _ : Fin Lt => μ_g) s)
      (fun t => sliceTWeight Ls N β (U_sl t) (U_sl (t + 1)))
      (fun t => measurable_sliceTWeight Ls N β (U_sl t) (U_sl (t + 1)))
      (fun t g => abs_sliceTWeight_le_one Ls N hN β hβ (U_sl t) (U_sl (t + 1)) g)
      (fun t => wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)))
      (fun t => integral_sliceTWeight Ls N β (U_sl t) (U_sl (t + 1)))
  rw [h_pi_eq]
  have h_prod_cast :
      (((∏ t : Fin Lt, wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)) : ℝ) : ℂ)) =
        ∏ t : Fin Lt, ((wilson4DSliceKernel Ls N β (U_sl t) (U_sl (t + 1)) : ℝ) : ℂ) := by
    induction (Finset.univ : Finset (Fin Lt)) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul, ih]
  rw [h_prod_cast, ← Finset.prod_mul_distrib]

/-- Open-chain convolution kernel `K_chain(fs)(U, V)` for intermediate slice weights `fs : List (A → ℂ)`. -/
noncomputable def wilson4DChainKernel (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    List (GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) →
    GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
    GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ
  | [], U, V => ((wilson4DSliceKernel Ls N β U V : ℝ) : ℂ)
  | f :: fs, U, V =>
    ∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) * f W *
      wilson4DChainKernel Ls N β fs W V ∂(latticeHaarMeasure Ls N)

private theorem measurable_integral_prod_right_aux {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : MeasureTheory.Measure β) [MeasureTheory.SFinite ν]
    (g : α → β → ℂ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun a => ∫ b, g a b ∂ν) :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := ν)
    hg.stronglyMeasurable).measurable

private noncomputable def absChainKernel {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (K : α → α → ℝ) :
    List (α → ℂ) → α → α → ℂ
  | [], U, V => ((K U V : ℝ) : ℂ)
  | f :: fs, U, V => ∫ W, ((K U W : ℝ) : ℂ) * f W * absChainKernel μ K fs W V ∂μ

private theorem wilson4DChainKernel_eq_abs (Ls N : ℕ) [NeZero Ls] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (fs : List (GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (U V : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilson4DChainKernel Ls N β fs U V =
      absChainKernel (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β) fs U V := by
  induction fs generalizing U with
  | nil => rfl
  | cons f fs ih =>
    dsimp [wilson4DChainKernel, absChainKernel]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    dsimp only
    rw [ih W]

private theorem absChainKernel_meta {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_m : Measurable (Function.uncurry K))
    (hK_bd : ∀ A B, 0 ≤ K A B ∧ K A B ≤ 1)
    (M : ℝ) (hM : 0 ≤ M)
    (fs : List (α → ℂ))
    (hmf : ∀ f ∈ fs, Measurable f) (hbf : ∀ f ∈ fs, ∀ W, ‖f W‖ ≤ M) :
    Measurable (Function.uncurry (absChainKernel μ K fs)) ∧
      (∀ A B, ‖absChainKernel μ K fs A B‖ ≤ M ^ fs.length) := by
  induction fs with
  | nil =>
    refine ⟨Complex.continuous_ofReal.measurable.comp hK_m, fun A B => ?_⟩
    dsimp [absChainKernel]
    have hb := hK_bd A B
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  | cons f fs ih =>
    have hmf' : ∀ g ∈ fs, Measurable g := fun g hg => hmf g (by simp [hg])
    have hbf' : ∀ g ∈ fs, ∀ W, ‖g W‖ ≤ M := fun g hg => hbf g (by simp [hg])
    obtain ⟨hm_fs, hb_fs⟩ := ih hmf' hbf'
    have hm_f := hmf f (by simp)
    have hb_f := hbf f (by simp)
    have hk_c : Measurable (fun p : α × α => ((K p.1 p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hK_m
    have hm_prod : Measurable (fun q : (α × α) × α =>
        ((K q.1.1 q.2 : ℝ) : ℂ) * f q.2 * absChainKernel μ K fs q.2 q.1.2) := by
      have hk : Measurable (fun q : (α × α) × α => ((K q.1.1 q.2 : ℝ) : ℂ)) :=
        hk_c.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have hf : Measurable (fun q : (α × α) × α => f q.2) := hm_f.comp measurable_snd
      have hc : Measurable (fun q : (α × α) × α => absChainKernel μ K fs q.2 q.1.2) :=
        hm_fs.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      exact (hk.mul hf).mul hc
    have h_bd_all : ∀ A B W,
        ‖((K A W : ℝ) : ℂ) * f W * absChainKernel μ K fs W B‖ ≤ M ^ (fs.length + 1) := by
      intro A B W
      have hk := hK_bd A W
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1, pow_succ]
      calc K A W * ‖f W‖ * ‖absChainKernel μ K fs W B‖
          ≤ 1 * M * M ^ fs.length :=
            mul_le_mul (mul_le_mul hk.2 (hb_f W) (norm_nonneg _) zero_le_one)
              (hb_fs W B) (norm_nonneg _) (mul_nonneg zero_le_one hM)
        _ = M ^ fs.length * M := by ring
    have hm_int : Measurable (fun p : α × α =>
        ∫ W, ((K p.1 W : ℝ) : ℂ) * f W * absChainKernel μ K fs W p.2 ∂μ) :=
      measurable_integral_prod_right_aux μ
        (fun (p : α × α) (W : α) => ((K p.1 W : ℝ) : ℂ) * f W * absChainKernel μ K fs W p.2) hm_prod
    refine ⟨hm_int, fun A B => ?_⟩
    have hm_in : Measurable (fun W => ((K A W : ℝ) : ℂ) * f W * absChainKernel μ K fs W B) :=
      ((hk_c.comp ((measurable_const : Measurable fun _ : α => A).prodMk measurable_id)).mul
        hm_f).mul
        (hm_fs.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : α => B)))
    have h_int := integrable_of_measurable_bound μ _ hm_in (M ^ (fs.length + 1)) (h_bd_all A B)
    calc ‖absChainKernel μ K (f :: fs) A B‖
        ≤ ∫ W, ‖((K A W : ℝ) : ℂ) * f W * absChainKernel μ K fs W B‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ _W, M ^ (fs.length + 1) ∂μ :=
            MeasureTheory.integral_mono h_int.norm (MeasureTheory.integrable_const _) (h_bd_all A B)
      _ = M ^ (fs.length + 1) := by simp [Measure.real, MeasureTheory.measure_univ]

private theorem wilson4DChainKernel_meta (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (M : ℝ) (hM : 0 ≤ M)
    (fs : List (GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (hmf : ∀ f ∈ fs, Measurable f) (hbf : ∀ f ∈ fs, ∀ W, ‖f W‖ ≤ M) :
    Measurable (Function.uncurry (wilson4DChainKernel Ls N β fs)) ∧
      (∀ A B, ‖wilson4DChainKernel Ls N β fs A B‖ ≤ M ^ fs.length) := by
  haveI := latticeHaarMeasure_prob Ls N
  have hm := absChainKernel_meta (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β)
    (continuous_wilson4DSliceKernel Ls N hN β hβ).measurable
    (wilson4DSliceKernel_bounds Ls N hN β hβ) M hM fs hmf hbf
  have h_eq : Function.uncurry (wilson4DChainKernel Ls N β fs) =
      Function.uncurry (absChainKernel (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β) fs) :=
    funext fun p => wilson4DChainKernel_eq_abs Ls N β fs p.1 p.2
  refine ⟨h_eq ▸ hm.1, fun A B => ?_⟩
  rw [wilson4DChainKernel_eq_abs]
  exact hm.2 A B

private theorem absChainKernel_append {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_m : Measurable (Function.uncurry K))
    (hK_bd : ∀ A B, 0 ≤ K A B ∧ K A B ≤ 1)
    (fs₁ fs₂ : List (α → ℂ)) (f_mid : α → ℂ)
    (h_m1 : ∀ f ∈ fs₁, Measurable f) (h_m_mid : Measurable f_mid) (h_m2 : ∀ f ∈ fs₂, Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (h_b1 : ∀ f ∈ fs₁, ∀ W, ‖f W‖ ≤ M) (h_b_mid : ∀ W, ‖f_mid W‖ ≤ M)
    (h_b2 : ∀ f ∈ fs₂, ∀ W, ‖f W‖ ≤ M)
    (U V : α) :
    absChainKernel μ K (fs₁ ++ f_mid :: fs₂) U V =
      ∫ W, absChainKernel μ K fs₁ U W * f_mid W * absChainKernel μ K fs₂ W V ∂μ := by
  induction fs₁ generalizing U with
  | nil => rfl
  | cons f₁ fs₁ ih =>
    have hmf₁' : ∀ f ∈ fs₁, Measurable f := fun f hf => h_m1 f (by simp [hf])
    have hbf₁' : ∀ f ∈ fs₁, ∀ W, ‖f W‖ ≤ M := fun f hf => h_b1 f (by simp [hf])
    have ih_W : ∀ W', absChainKernel μ K (fs₁ ++ f_mid :: fs₂) W' V =
        ∫ W, absChainKernel μ K fs₁ W' W * f_mid W * absChainKernel μ K fs₂ W V ∂μ :=
      fun W' => ih hmf₁' hbf₁' W'
    dsimp [absChainKernel]
    simp_rw [ih_W]
    obtain ⟨hm_1, hb_1⟩ := absChainKernel_meta μ K hK_m hK_bd M hM fs₁ hmf₁' hbf₁'
    obtain ⟨hm_2, hb_2⟩ := absChainKernel_meta μ K hK_m hK_bd M hM fs₂ h_m2 h_b2
    have h_fubini : MeasureTheory.Integrable
        (Function.uncurry fun W' W =>
          ((K U W' : ℝ) : ℂ) * f₁ W' *
            (absChainKernel μ K fs₁ W' W * f_mid W * absChainKernel μ K fs₂ W V)) (μ.prod μ) := by
      have hk_c : Measurable (fun p : α × α => ((K p.1 p.2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp hK_m
      have hm_left : Measurable (fun p : α × α => ((K U p.1 : ℝ) : ℂ) * f₁ p.1) :=
        (hk_c.comp (measurable_const.prodMk measurable_fst)).mul
          ((h_m1 f₁ (by simp)).comp measurable_fst)
      have hm_right : Measurable (fun p : α × α =>
          absChainKernel μ K fs₁ p.1 p.2 * f_mid p.2 * absChainKernel μ K fs₂ p.2 V) :=
        (hm_1.mul (h_m_mid.comp measurable_snd)).mul
          (hm_2.comp (measurable_snd.prodMk measurable_const))
      refine (MeasureTheory.integrable_const (M ^ (fs₁.length + 1 + 1 + fs₂.length))).mono'
        (hm_left.mul hm_right).stronglyMeasurable.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun p => ?_
      dsimp only [Function.uncurry]
      have hk := hK_bd U p.1
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk.1]
      have h1 : K U p.1 * ‖f₁ p.1‖ ≤ 1 * M :=
        mul_le_mul hk.2 (h_b1 f₁ (by simp) p.1) (norm_nonneg _) zero_le_one
      have h2 : ‖absChainKernel μ K fs₁ p.1 p.2‖ * ‖f_mid p.2‖ ≤ M ^ fs₁.length * M :=
        mul_le_mul (hb_1 p.1 p.2) (h_b_mid p.2) (norm_nonneg _) (pow_nonneg hM _)
      have h3 : ‖absChainKernel μ K fs₁ p.1 p.2‖ * ‖f_mid p.2‖ *
            ‖absChainKernel μ K fs₂ p.2 V‖ ≤ M ^ fs₁.length * M * M ^ fs₂.length :=
        mul_le_mul h2 (hb_2 p.2 V) (norm_nonneg _) (mul_nonneg (pow_nonneg hM _) hM)
      calc K U p.1 * ‖f₁ p.1‖ *
              (‖absChainKernel μ K fs₁ p.1 p.2‖ * ‖f_mid p.2‖ *
                ‖absChainKernel μ K fs₂ p.2 V‖)
          ≤ (1 * M) * (M ^ fs₁.length * M * M ^ fs₂.length) :=
            mul_le_mul h1 h3
              (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
              (mul_nonneg zero_le_one hM)
        _ = M ^ (fs₁.length + 1 + 1 + fs₂.length) := by rw [pow_add, pow_add, pow_add]; ring
    have h_l_eq :
        (∫ W', ((K U W' : ℝ) : ℂ) * f₁ W' *
            (∫ W, absChainKernel μ K fs₁ W' W * f_mid W * absChainKernel μ K fs₂ W V ∂μ) ∂μ) =
        ∫ W', ∫ W, ((K U W' : ℝ) : ℂ) * f₁ W' *
            (absChainKernel μ K fs₁ W' W * f_mid W * absChainKernel μ K fs₂ W V) ∂μ ∂μ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W' => ?_)
      dsimp only
      exact (MeasureTheory.integral_const_mul _ _).symm
    have h_r_eq :
        (∫ W, (∫ W', ((K U W' : ℝ) : ℂ) * f₁ W' * absChainKernel μ K fs₁ W' W ∂μ) * f_mid W *
              absChainKernel μ K fs₂ W V ∂μ) =
        ∫ W, ∫ W', ((K U W' : ℝ) : ℂ) * f₁ W' *
            (absChainKernel μ K fs₁ W' W * f_mid W * absChainKernel μ K fs₂ W V) ∂μ ∂μ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      dsimp only
      rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W' => ?_)
      dsimp only
      ring
    rw [h_l_eq, h_r_eq, MeasureTheory.integral_integral_swap h_fubini]

theorem wilson4DChainKernel_append (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (fs₁ fs₂ : List (GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (f_mid : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (h_m1 : ∀ f ∈ fs₁, Measurable f) (h_m_mid : Measurable f_mid) (h_m2 : ∀ f ∈ fs₂, Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (h_b1 : ∀ f ∈ fs₁, ∀ W, ‖f W‖ ≤ M) (h_b_mid : ∀ W, ‖f_mid W‖ ≤ M) (h_b2 : ∀ f ∈ fs₂, ∀ W, ‖f W‖ ≤ M)
    (U V : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilson4DChainKernel Ls N β (fs₁ ++ f_mid :: fs₂) U V =
      ∫ W, wilson4DChainKernel Ls N β fs₁ U W * f_mid W *
        wilson4DChainKernel Ls N β fs₂ W V ∂(latticeHaarMeasure Ls N) := by
  haveI := latticeHaarMeasure_prob Ls N
  simp_rw [wilson4DChainKernel_eq_abs]
  exact absChainKernel_append (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β)
    (continuous_wilson4DSliceKernel Ls N hN β hβ).measurable
    (wilson4DSliceKernel_bounds Ls N hN β hβ)
    fs₁ fs₂ f_mid h_m1 h_m_mid h_m2 M hM h_b1 h_b_mid h_b2 U V

theorem wilson4DTransferOp_pow_apply_ae (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure Ls N)) (k : ℕ) :
    ⇑(((wilson4DTransferOp Ls N hN β hβ) ^ (k + 1)) ψ) =ᵐ[latticeHaarMeasure Ls N]
      fun U => ∫ V, wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) U V * ψ V
        ∂(latticeHaarMeasure Ls N) := by
  let μ := latticeHaarMeasure Ls N
  haveI := latticeHaarMeasure_prob Ls N
  let T := wilson4DTransferOp Ls N hN β hβ
  induction k with
  | zero =>
    simpa [wilson4DChainKernel, wilson4DSliceKernel, wilsonIntegralFn] using
      wilsonIntegralOp_apply_ae Ls N β hβ (wilson4DKernel Ls N β)
        (continuous_wilson4DKernel Ls N hN β hβ)
        (fun A B => (Real.exp_pos _).le.trans (wilson4DKernel_bounds Ls N hN β hβ A B).1)
        1 zero_le_one
        (fun A B => (wilson4DKernel_bounds Ls N hN β hβ A B).2) ψ
  | succ k ih =>
    have h_pow : (T ^ (k + 2)) ψ = T ((T ^ (k + 1)) ψ) := by
      rw [pow_succ']; rfl
    rw [h_pow]
    have hT := wilsonIntegralOp_apply_ae Ls N β hβ (wilson4DKernel Ls N β)
      (continuous_wilson4DKernel Ls N hN β hβ)
      (fun A B => (Real.exp_pos _).le.trans (wilson4DKernel_bounds Ls N hN β hβ A B).1)
      1 zero_le_one
      (fun A B => (wilson4DKernel_bounds Ls N hN β hβ A B).2) ((T ^ (k + 1)) ψ)
    filter_upwards [hT] with U hTU
    have hTU' : (T ((T ^ (k + 1)) ψ)) U =
        wilsonIntegralFn Ls N β (wilson4DKernel Ls N β) ((T ^ (k + 1)) ψ) U := hTU
    rw [hTU']
    dsimp [wilsonIntegralFn]
    have h_inner_sub :
        (∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) * ((T ^ (k + 1)) ψ) W ∂μ) =
        ∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) *
          (∫ V, wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) W V * ψ V ∂μ) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ih] with W hW
      rw [hW]
    change (∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) * ((T ^ (k + 1)) ψ) W ∂μ) =
      ∫ V, wilson4DChainKernel Ls N β (List.replicate (k + 1) (fun _ => 1)) U V * ψ V ∂μ
    rw [h_inner_sub]
    obtain ⟨hm_k, hb_k⟩ := wilson4DChainKernel_meta Ls N hN β hβ 1 zero_le_one
      (List.replicate k (fun _ => 1))
      (fun f hf => by rw [List.mem_replicate] at hf; rw [hf.2]; exact measurable_const)
      (fun f hf W => by rw [List.mem_replicate] at hf; rw [hf.2]; simp)
    let G_L := GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)
    have h_fub : MeasureTheory.Integrable
        (Function.uncurry fun W V =>
          ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) *
            (wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) W V * ψ V)) (μ.prod μ) := by
      have hm_1 : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => ((wilson4DSliceKernel Ls N β U p.1 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.continuous_ofReal.comp (continuous_wilson4DSliceKernel Ls N hN β hβ)).measurable.comp
          (continuous_const.prodMk continuous_fst).measurable |>.stronglyMeasurable.aestronglyMeasurable
      have hm_2 : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) p.1 p.2)
          (μ.prod μ) := hm_k.stronglyMeasurable.aestronglyMeasurable
      have hm_3 : MeasureTheory.AEStronglyMeasurable (fun p : G_L × G_L => ψ p.2) (μ.prod μ) :=
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable.comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_snd
      have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
      have hψ_norm : MeasureTheory.Integrable (fun V => ‖ψ V‖) μ :=
        (hψ_mem.integrable one_le_two).norm
      have h_dom : MeasureTheory.Integrable
          (fun p : G_L × G_L => (1 : ℝ) * ‖ψ p.2‖) (μ.prod μ) :=
        (MeasureTheory.integrable_const (1 : ℝ)).mul_prod hψ_norm
      refine h_dom.mono' (hm_1.mul (hm_2.mul hm_3)) ?_
      refine Filter.Eventually.of_forall fun (p : G_L × G_L) => ?_
      dsimp only [Function.uncurry]
      have hk := wilson4DSliceKernel_bounds Ls N hN β hβ U p.1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1, one_mul]
      have hbk : ‖wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) p.1 p.2‖ ≤ 1 := by
        simpa using hb_k p.1 p.2
      calc wilson4DSliceKernel Ls N β U p.1 *
              (‖wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) p.1 p.2‖ * ‖ψ p.2‖)
          = (wilson4DSliceKernel Ls N β U p.1 *
              ‖wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) p.1 p.2‖) * ‖ψ p.2‖ := by ring
        _ ≤ 1 * ‖ψ p.2‖ := mul_le_mul_of_nonneg_right
              (mul_le_one₀ hk.2 (by positivity) hbk) (norm_nonneg _)
        _ = ‖ψ p.2‖ := one_mul _
    have h_l_eq :
        (∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) *
          (∫ V, wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) W V * ψ V ∂μ) ∂μ) =
        ∫ W, ∫ V, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) *
          (wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) W V * ψ V) ∂μ ∂μ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      dsimp only
      exact (MeasureTheory.integral_const_mul _ _).symm
    have h_r_eq :
        (∫ V, wilson4DChainKernel Ls N β (List.replicate (k + 1) (fun _ => 1)) U V * ψ V ∂μ) =
        ∫ V, ∫ W, ((wilson4DSliceKernel Ls N β U W : ℝ) : ℂ) *
          (wilson4DChainKernel Ls N β (List.replicate k (fun _ => 1)) W V * ψ V) ∂μ ∂μ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      dsimp only
      rw [List.replicate_succ]
      dsimp [wilson4DChainKernel]
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      dsimp only
      ring
    rw [h_l_eq, h_r_eq, MeasureTheory.integral_integral_swap h_fub]

private theorem absSlice_open_chain {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_m : Measurable (Function.uncurry K))
    (hK_bd : ∀ A B, 0 ≤ K A B ∧ K A B ≤ 1)
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs)
    (m : ℕ) (fs : Fin m → α → ℂ)
    (hmf : ∀ j, Measurable (fs j)) (hbf : ∀ j V, ‖fs j V‖ ≤ M_obs)
    (U_start U_end : α) :
    (∫ U : Fin m → α,
      ((K U_start (if h : 0 < m then U ⟨0, h⟩ else U_end) : ℝ) : ℂ) *
        (∏ j : Fin m, fs j (U j) * ((K (U j)
          (if h : j.val + 1 < m then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ))
      ∂(MeasureTheory.Measure.pi fun _ => μ)) =
    absChainKernel μ K (List.ofFn fs) U_start U_end := by
  induction m generalizing U_start with
  | zero =>
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi fun _ : Fin 0 => μ) := inferInstance
    simp only [lt_self_iff_false, ↓reduceDIte, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [MeasureTheory.integral_const]
    simp [absChainKernel, Measure.real, MeasureTheory.measure_univ]
  | succ m ih =>
    let F_int : (Fin (m + 1) → α) → ℂ := fun U =>
      ((K U_start (U 0) : ℝ) : ℂ) *
        (∏ j : Fin (m + 1), fs j (U j) * ((K (U j)
          (if h : j.val + 1 < m + 1 then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ))
    have hm_k : Measurable (fun p : α × α => ((K p.1 p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hK_m
    have hpi : ∀ i : Fin (m + 1), Measurable (fun U : Fin (m + 1) → α => U i) :=
      fun i => measurable_pi_apply i
    have hF_m : Measurable F_int := by
      refine (hm_k.comp (measurable_const.prodMk (hpi 0))).mul
        (Finset.measurable_prod Finset.univ fun j _ => ?_)
      have hmfj := (hmf j).comp (hpi j)
      by_cases hj : j.val + 1 < m + 1
      · simp_rw [dif_pos hj]
        exact hmfj.mul (hm_k.comp ((hpi j).prodMk (hpi ⟨j.val + 1, hj⟩)))
      · simp_rw [dif_neg hj]
        exact hmfj.mul (hm_k.comp ((hpi j).prodMk measurable_const))
    have hF_bd : ∀ U, ‖F_int U‖ ≤ M_obs ^ (m + 1) := fun U => by
      dsimp only [F_int]
      have h0 := hK_bd U_start (U 0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0.1]
      refine (mul_le_of_le_one_left (norm_nonneg _) h0.2).trans ?_
      refine norm_prod_fin_le _ M_obs hM_obs fun j => ?_
      have hj := hK_bd (U j)
        (if h : j.val + 1 < m + 1 then U ⟨j.val + 1, h⟩ else U_end)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hj.1]
      exact (mul_le_of_le_one_right (norm_nonneg _) hj.2).trans (hbf j _)
    have h_cons_eq : ∀ (x₀ : α) (U : Fin m → α),
        F_int (Fin.cons x₀ U) =
          (((K U_start x₀ : ℝ) : ℂ) * fs 0 x₀) *
            (((K x₀ (if h : 0 < m then U ⟨0, h⟩ else U_end) : ℝ) : ℂ) *
              ∏ j : Fin m, fs j.succ (U j) * ((K (U j)
                (if h : j.val + 1 < m then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ)) := by
      intro x₀ U
      dsimp only [F_int]
      rw [Fin.prod_univ_succ]
      have h0 : Fin.cons (α := fun _ => α) x₀ U 0 = x₀ := Fin.cons_zero (α := fun _ => α) x₀ U
      rw [h0]
      have h_next0 :
          (if h : (0 : Fin (m + 1)).val + 1 < m + 1 then
            Fin.cons (α := fun _ => α) x₀ U ⟨(0 : Fin (m + 1)).val + 1, h⟩ else U_end) =
          if h : 0 < m then U ⟨0, h⟩ else U_end := by
        by_cases hm : 0 < m
        · have h1 : (0 : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_zero]; omega
          rw [dif_pos h1, dif_pos hm]
          have h_idx : (⟨(0 : Fin (m + 1)).val + 1, h1⟩ : Fin (m + 1)) = (⟨0, hm⟩ : Fin m).succ := by
            apply Fin.ext; simp [Fin.val_succ]
          rw [h_idx]
          exact Fin.cons_succ (α := fun _ => α) x₀ U ⟨0, hm⟩
        · have h1 : ¬ ((0 : Fin (m + 1)).val + 1 < m + 1) := by simp only [Fin.val_zero]; omega
          rw [dif_neg h1, dif_neg hm]
      rw [h_next0]
      have h_tail :
          (∏ j : Fin m, fs j.succ (Fin.cons (α := fun _ => α) x₀ U j.succ) *
            ((K (Fin.cons (α := fun _ => α) x₀ U j.succ)
              (if h : j.succ.val + 1 < m + 1 then
                Fin.cons (α := fun _ => α) x₀ U ⟨j.succ.val + 1, h⟩ else U_end) : ℝ) : ℂ)) =
          ∏ j : Fin m, fs j.succ (U j) * ((K (U j)
            (if h : j.val + 1 < m then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Fin.cons_succ]
        by_cases hj : j.val + 1 < m
        · have hj' : j.succ.val + 1 < m + 1 := by simp [Fin.val_succ]; omega
          rw [dif_pos hj', dif_pos hj]
          have h_idx : (⟨j.succ.val + 1, hj'⟩ : Fin (m + 1)) = (⟨j.val + 1, hj⟩ : Fin m).succ := by
            apply Fin.ext; simp [Fin.val_succ]
          rw [h_idx, Fin.cons_succ]
        · have hj' : ¬ (j.succ.val + 1 < m + 1) := by simp [Fin.val_succ]; omega
          rw [dif_neg hj', dif_neg hj]
      rw [h_tail]
      ring
    have h_rew0 :
        (∫ U : Fin (m + 1) → α,
          ((K U_start (if h : 0 < m + 1 then U ⟨0, h⟩ else U_end) : ℝ) : ℂ) *
            (∏ j : Fin (m + 1), fs j (U j) * ((K (U j)
              (if h : j.val + 1 < m + 1 then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ))
          ∂(MeasureTheory.Measure.pi fun _ => μ)) =
        ∫ U : Fin (m + 1) → α, F_int U ∂(MeasureTheory.Measure.pi fun _ => μ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      dsimp only [F_int]
      rw [dif_pos (Nat.zero_lt_succ m)]
      rfl
    rw [h_rew0, integral_pi_fin_head μ m F_int hF_m (M_obs ^ (m + 1)) hF_bd]
    have h_step_eq :
        (∫ x₀ : α, ∫ U : Fin m → α, F_int (Fin.cons x₀ U)
            ∂(MeasureTheory.Measure.pi fun _ => μ) ∂μ) =
        ∫ x₀ : α, (((K U_start x₀ : ℝ) : ℂ) * fs 0 x₀) *
          absChainKernel μ K (List.ofFn fun j : Fin m => fs j.succ) x₀ U_end ∂μ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
      dsimp only
      simp_rw [h_cons_eq x₀]
      rw [MeasureTheory.integral_const_mul,
        ih (fun j => fs j.succ) (fun j => hmf j.succ) (fun j => hbf j.succ) x₀]
    rw [h_step_eq, List.ofFn_succ]
    rfl

private theorem wilson4DSlice_open_chain (Ls N : ℕ) [NeZero Ls] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs)
    (m : ℕ) (fs : Fin m → GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hmf : ∀ j, Measurable (fs j)) (hbf : ∀ j V, ‖fs j V‖ ≤ M_obs)
    (U_start U_end : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (∫ U : Fin m → GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ),
      ((wilson4DSliceKernel Ls N β U_start (if h : 0 < m then U ⟨0, h⟩ else U_end) : ℝ) : ℂ) *
        (∏ j : Fin m, fs j (U j) * ((wilson4DSliceKernel Ls N β (U j)
          (if h : j.val + 1 < m then U ⟨j.val + 1, h⟩ else U_end) : ℝ) : ℂ))
      ∂(MeasureTheory.Measure.pi fun _ => latticeHaarMeasure Ls N)) =
    wilson4DChainKernel Ls N β (List.ofFn fs) U_start U_end := by
  haveI := latticeHaarMeasure_prob Ls N
  rw [wilson4DChainKernel_eq_abs]
  exact absSlice_open_chain (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β)
    (continuous_wilson4DSliceKernel Ls N hN β hβ).measurable
    (wilson4DSliceKernel_bounds Ls N hN β hβ) M_obs hM_obs m fs hmf hbf U_start U_end

private theorem absSlice_closed_chain {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_m : Measurable (Function.uncurry K))
    (hK_bd : ∀ A B, 0 ≤ K A B ∧ K A B ≤ 1)
    (n : ℕ) (obs : Fin (n + 1) → α → ℂ)
    (h_meas : ∀ t, Measurable (obs t))
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs) (h_bd : ∀ t V, ‖obs t V‖ ≤ M_obs) :
    (∫ U : Fin (n + 1) → α,
      ∏ i : Fin (n + 1), obs i (U i) * ((K (U i) (U (i + 1)) : ℝ) : ℂ)
      ∂(MeasureTheory.Measure.pi fun _ => μ)) =
    ∫ U₀ : α, obs 0 U₀ * absChainKernel μ K (List.ofFn fun j : Fin n => obs j.succ) U₀ U₀ ∂μ := by
  let F_closed : (Fin (n + 1) → α) → ℂ := fun U =>
    ∏ i : Fin (n + 1), obs i (U i) * ((K (U i) (U (i + 1)) : ℝ) : ℂ)
  have hm_k : Measurable (fun p : α × α => ((K p.1 p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hK_m
  have hpi : ∀ i : Fin (n + 1), Measurable (fun U : Fin (n + 1) → α => U i) :=
    fun i => measurable_pi_apply i
  have hF_m : Measurable F_closed :=
    Finset.measurable_prod Finset.univ fun i _ =>
      ((h_meas i).comp (hpi i)).mul (hm_k.comp ((hpi i).prodMk (hpi (i + 1))))
  have hF_bd : ∀ U, ‖F_closed U‖ ≤ M_obs ^ (n + 1) := fun U =>
    norm_prod_fin_le _ M_obs hM_obs fun i => by
      have hb := hK_bd (U i) (U (i + 1))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact (mul_le_of_le_one_right (norm_nonneg _) hb.2).trans (h_bd _ _)
  have h_closed_cons : ∀ (U₀ : α) (U : Fin n → α),
      F_closed (Fin.cons U₀ U) =
        obs 0 U₀ *
          (((K U₀ (if h : 0 < n then U ⟨0, h⟩ else U₀) : ℝ) : ℂ) *
            ∏ j : Fin n, obs j.succ (U j) * ((K (U j)
              (if h : j.val + 1 < n then U ⟨j.val + 1, h⟩ else U₀) : ℝ) : ℂ)) := by
    intro U₀ U
    dsimp only [F_closed]
    rw [Fin.prod_univ_succ]
    have h0 : Fin.cons (α := fun _ => α) U₀ U 0 = U₀ := Fin.cons_zero (α := fun _ => α) U₀ U
    rw [h0]
    have h_next0 : Fin.cons (α := fun _ => α) U₀ U ((0 : Fin (n + 1)) + 1) =
        if h : 0 < n then U ⟨0, h⟩ else U₀ := by
      by_cases hn : 0 < n
      · rw [dif_pos hn]
        have h1 : (0 : Fin (n + 1)) + 1 = (⟨0, hn⟩ : Fin n).succ := by
          apply Fin.ext
          simp [Fin.val_add, Fin.val_succ, Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
        rw [h1]
        exact Fin.cons_succ (α := fun _ => α) U₀ U ⟨0, hn⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [dif_neg hn]
        have h1 : (0 : Fin 1) + 1 = 0 := Fin.ext rfl
        rw [h1]
        exact Fin.cons_zero (α := fun _ => α) U₀ U
    rw [h_next0]
    have h_tail :
        (∏ j : Fin n, obs j.succ (Fin.cons (α := fun _ => α) U₀ U j.succ) *
          ((K (Fin.cons (α := fun _ => α) U₀ U j.succ)
            (Fin.cons (α := fun _ => α) U₀ U (j.succ + 1)) : ℝ) : ℂ)) =
        ∏ j : Fin n, obs j.succ (U j) * ((K (U j)
          (if h : j.val + 1 < n then U ⟨j.val + 1, h⟩ else U₀) : ℝ) : ℂ) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fin.cons_succ]
      by_cases hj : j.val + 1 < n
      · rw [dif_pos hj]
        have h_idx : j.succ + 1 = (⟨j.val + 1, hj⟩ : Fin n).succ := by
          apply Fin.ext
          simp [Fin.val_add, Fin.val_succ,
            Nat.mod_eq_of_lt (by omega : j.val + 1 + 1 < n + 1)]
        rw [h_idx, Fin.cons_succ]
      · rw [dif_neg hj]
        have h_wrap : j.succ + 1 = (0 : Fin (n + 1)) := by
          apply Fin.ext
          have hj_eq : j.val + 1 = n := by omega
          simp [Fin.val_add, Fin.val_succ, hj_eq]
        rw [h_wrap, Fin.cons_zero]
    rw [h_tail]
    ring
  change (∫ U : Fin (n + 1) → α, F_closed U ∂(MeasureTheory.Measure.pi fun _ => μ)) = _
  rw [integral_pi_fin_head μ n F_closed hF_m (M_obs ^ (n + 1)) hF_bd]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U₀ => ?_)
  dsimp only
  simp_rw [h_closed_cons U₀]
  rw [MeasureTheory.integral_const_mul,
    absSlice_open_chain μ K hK_m hK_bd M_obs hM_obs n (fun j => obs j.succ)
      (fun j => h_meas _) (fun j => h_bd _) U₀ U₀]

private theorem slice_closed_chain_succ (Ls n N : ℕ) [NeZero Ls]
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin (n + 1) →
      GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (h_meas : ∀ t, Measurable (obs t))
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs) (h_bd : ∀ t V, ‖obs t V‖ ≤ M_obs) :
    ((cubic4PartitionFn Ls (n + 1) N β : ℝ) : ℂ) *
      cubic4Schwinger Ls (n + 1) N β (n + 1)
        (fun t U => obs t ((slice4DFieldEquiv Ls (n + 1) N U).1 t)) =
      ∫ U₀, obs 0 U₀ *
        wilson4DChainKernel Ls N β
          (List.ofFn fun j : Fin n => obs j.succ) U₀ U₀
        ∂(latticeHaarMeasure Ls N) := by
  haveI := latticeHaarMeasure_prob Ls N
  rw [cubic4Schwinger_eq_slice_integral Ls (n + 1) N hN β hβ obs h_meas M_obs hM_obs h_bd]
  have h_abs := absSlice_closed_chain (latticeHaarMeasure Ls N) (wilson4DSliceKernel Ls N β)
    (continuous_wilson4DSliceKernel Ls N hN β hβ).measurable
    (wilson4DSliceKernel_bounds Ls N hN β hβ) n obs h_meas M_obs hM_obs h_bd
  rw [h_abs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U₀ => ?_)
  dsimp only
  rw [wilson4DChainKernel_eq_abs]

/-- Explicit closed-chain transfer theorem for arbitrary bounded measurable slice observables. -/
theorem slice_closed_chain_eq_chainTrace (Ls Lt N : ℕ) [NeZero Ls] [instLt : NeZero Lt]
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin Lt →
      GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (h_meas : ∀ t, Measurable (obs t))
    (M_obs : ℝ) (hM_obs : 0 ≤ M_obs) (h_bd : ∀ t V, ‖obs t V‖ ≤ M_obs) :
    ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) *
      cubic4Schwinger Ls Lt N β Lt (fun t U => obs t ((slice4DFieldEquiv Ls Lt N U).1 t)) =
      ∫ U₀, obs 0 U₀ *
        wilson4DChainKernel Ls N β
          (List.ofFn fun j : Fin (Lt - 1) =>
            obs ⟨j.val + 1, by have := NeZero.pos Lt; omega⟩) U₀ U₀
        ∂(latticeHaarMeasure Ls N) := by
  revert instLt
  rcases Lt with _ | n
  · intro inst0
    exact absurd rfl inst0.out
  · intro _
    exact slice_closed_chain_succ Ls n N hN β hβ obs h_meas M_obs hM_obs h_bd

/--
**Exact finite-volume trace formula for `cubic4PartitionFn`**:
for all `Ls, Lt ≥ 1`, `N ≥ 1`, `β ≥ 0`,
`cubic4PartitionFn Ls Lt N β = ∫ U₀, (wilson4DChainKernel Ls N β (List.replicate (Lt - 1) 1) U₀ U₀).re dμ(U₀)`.
-/
theorem cubic4PartitionFn_eq_chainTrace (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) =
      ∫ U₀, wilson4DChainKernel Ls N β (List.replicate (Lt - 1) (fun _ => 1)) U₀ U₀
        ∂(latticeHaarMeasure Ls N) := by
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  have h_sl := slice_closed_chain_eq_chainTrace Ls Lt N hN β hβ (fun _ _ => 1)
    (fun _ => measurable_const) 1 zero_le_one (fun _ _ => by simp)
  have h_schw1 : cubic4Schwinger Ls Lt N β Lt (fun _ _ => 1) = 1 := by
    unfold cubic4Schwinger
    simp only [Finset.prod_const_one, one_mul]
    have hZ_pos : 0 < cubic4PartitionFn Ls Lt N β := cubic4PartitionFn_pos Ls Lt N β hβ
    have h_int_c : MeasureTheory.Integrable
        (fun U => ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))
        (spacetimeHaarMeasure Ls Lt N) := by
      refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
        (Complex.continuous_ofReal.measurable.comp
          (measurable_cubic4WilsonWeight Ls Lt N β)).stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun U => by
          have hb := cubic4WilsonWeight_bounds Ls Lt N β hβ U
          have hnn : 0 ≤ cubic4WilsonWeight Ls Lt N β U := by
            unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]; exact hb.2)
    have hre : (∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)).re =
        cubic4PartitionFn Ls Lt N β := by
      change RCLike.re (∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
        ∂(spacetimeHaarMeasure Ls Lt N)) = cubic4PartitionFn Ls Lt N β
      rw [← integral_re h_int_c]; rfl
    have him : (∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)).im = 0 := by
      have h1 : (∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)).im =
          RCLike.re (-Complex.I * ∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_int_c.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun U => ?_)
      simp [Complex.mul_re]
    have h_int_eq :
        (∫ U, ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)) =
          ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) :=
      Complex.ext hre him
    rw [h_int_eq, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hZ_pos.ne',
      Complex.ofReal_one]
  rw [h_schw1, mul_one] at h_sl
  rw [h_sl]
  simp only [one_mul]
  have h_rep :
      (List.ofFn fun _ : Fin (Lt - 1) =>
        (fun _ : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) => (1 : ℂ))) =
      List.replicate (Lt - 1) (fun _ => 1) := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => by simp
  rw [h_rep]

/--
**Two-slice 4D Feynman–Kac correlator formula (`0 < k < Lt`)**:
factors `cubic4Schwinger` of `A` at slice `0` and `B` at slice `k` through the
Chapman–Kolmogorov iterated kernels `K_slice^(k)` and `K_slice^(Lt - k)` of `wilson4DTransferOp`.
-/
theorem cubic4Schwinger_two_slice_eq_wilson4D (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < Lt)
    (A B : GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hA_m : Measurable A) (hB_m : Measurable B)
    (M : ℝ) (hM : 1 ≤ M) (hA_bd : ∀ V, ‖A V‖ ≤ M) (hB_bd : ∀ V, ‖B V‖ ≤ M) :
    ((cubic4PartitionFn Ls Lt N β : ℝ) : ℂ) *
      cubic4Schwinger Ls Lt N β 2
        ![fun U => A ((slice4DFieldEquiv Ls Lt N U).1 0),
          fun U => B ((slice4DFieldEquiv Ls Lt N U).1 ⟨k, hk_lt⟩)] =
      ∫ U₀, A U₀ * ∫ Uk,
        wilson4DChainKernel Ls N β (List.replicate (k - 1) (fun _ => 1)) U₀ Uk * B Uk *
        wilson4DChainKernel Ls N β (List.replicate (Lt - k - 1) (fun _ => 1)) Uk U₀
        ∂(latticeHaarMeasure Ls N) ∂(latticeHaarMeasure Ls N) := by
  let G_L := GaugeField (cubicTorus3 Ls) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let obs : Fin Lt → G_L → ℂ := fun t =>
    if t.val = 0 then A else if t.val = k then B else fun _ => 1
  have h_obs_m : ∀ t, Measurable (obs t) := fun t => by
    dsimp [obs]; split_ifs <;> first | exact hA_m | exact hB_m | exact measurable_const
  have h_obs_bd : ∀ t V, ‖obs t V‖ ≤ M := fun t V => by
    dsimp [obs]; split_ifs
    · exact hA_bd V
    · exact hB_bd V
    · simpa using hM
  have h_schw_eq :
      cubic4Schwinger Ls Lt N β 2
          ![fun U => A ((slice4DFieldEquiv Ls Lt N U).1 0),
            fun U => B ((slice4DFieldEquiv Ls Lt N U).1 ⟨k, hk_lt⟩)] =
        cubic4Schwinger Ls Lt N β Lt (fun t U => obs t ((slice4DFieldEquiv Ls Lt N U).1 t)) := by
    unfold cubic4Schwinger
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    congr 1
    dsimp only
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    let t0 : Fin Lt := ⟨0, NeZero.pos Lt⟩
    let tk : Fin Lt := ⟨k, hk_lt⟩
    have h0k : t0 ≠ tk := fun h => hk_pos.ne' (congrArg Fin.val h).symm
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t0)]
    have htk_mem : tk ∈ Finset.univ.erase t0 := Finset.mem_erase.mpr ⟨h0k.symm, Finset.mem_univ tk⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase t0) _ htk_mem]
    have h_rest : ∏ t ∈ (Finset.univ.erase t0).erase tk,
        obs t ((slice4DFieldEquiv Ls Lt N U).1 t) = 1 := by
      refine Finset.prod_eq_one fun t ht => ?_
      have hntk : t ≠ tk := (Finset.mem_erase.mp ht).1
      have hnt0 : t ≠ t0 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
      have hvk : t.val ≠ k := fun h => hntk (Fin.ext h)
      simp [obs, show t ≠ 0 from hnt0, hvk]
    have ht0_val : obs t0 ((slice4DFieldEquiv Ls Lt N U).1 t0) =
        A ((slice4DFieldEquiv Ls Lt N U).1 0) := by
      have h0eq : t0 = 0 := Fin.ext rfl
      rw [h0eq]
      simp [obs]
    have htk_val : obs tk ((slice4DFieldEquiv Ls Lt N U).1 tk) =
        B ((slice4DFieldEquiv Ls Lt N U).1 ⟨k, hk_lt⟩) := by
      simp [obs, tk, hk_pos.ne']
    rw [h_rest, mul_one, ht0_val, htk_val]
  rw [h_schw_eq, slice_closed_chain_eq_chainTrace Ls Lt N hN β hβ obs h_obs_m M (by linarith) h_obs_bd]
  have h0_obs : obs 0 = A := by simp [obs]
  have h_list_eq :
      (List.ofFn fun j : Fin (Lt - 1) => obs ⟨j.val + 1, by have := NeZero.pos Lt; omega⟩) =
        List.replicate (k - 1) (fun _ => 1) ++ B :: List.replicate (Lt - k - 1) (fun _ => 1) := by
    refine List.ext_getElem ?_ ?_
    · simp only [List.length_ofFn, List.length_append, List.length_cons, List.length_replicate]
      omega
    · intro i hi1 hi2
      rw [List.getElem_ofFn]
      have hi_lt : i < Lt - 1 := by simpa using hi1
      have h_ne0 : (⟨i + 1, by omega⟩ : Fin Lt).val ≠ 0 := by simp
      by_cases hik : i = k - 1
      · subst hik
        have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
        simp only [obs, h_ne0, hk1, hk_pos.ne', ↓reduceIte]
        rw [List.getElem_append_right (by simp)]
        simp
      · by_cases hilt : i < k - 1
        · have h_nek : (⟨i + 1, by omega⟩ : Fin Lt).val ≠ k := by simp; omega
          simp only [obs, h_ne0, ↓reduceIte, h_nek]
          rw [List.getElem_append_left (by simp [hilt]), List.getElem_replicate]
        · have h_gt : k - 1 < i := by omega
          have h_nek : (⟨i + 1, by omega⟩ : Fin Lt).val ≠ k := by simp; omega
          simp only [obs, h_ne0, ↓reduceIte, h_nek]
          have hpos : i - (k - 1) ≠ 0 := by omega
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
          rw [List.getElem_append_right (by simp; omega)]
          simp only [hj, List.length_replicate, List.getElem_cons_succ, List.getElem_replicate]
          rfl
  rw [h0_obs, h_list_eq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U₀ => ?_)
  dsimp only
  congr 1
  exact wilson4DChainKernel_append Ls N hN β hβ
    (List.replicate (k - 1) (fun _ => 1))
    (List.replicate (Lt - k - 1) (fun _ => 1)) B
    (fun f hf => by rw [List.mem_replicate] at hf; rw [hf.2]; exact measurable_const)
    hB_m
    (fun f hf => by rw [List.mem_replicate] at hf; rw [hf.2]; exact measurable_const)
    M (by linarith : 0 ≤ M)
    (fun f hf W => by rw [List.mem_replicate] at hf; rw [hf.2]; simpa using hM)
    hB_bd
    (fun f hf W => by rw [List.mem_replicate] at hf; rw [hf.2]; simpa using hM)
    U₀ U₀

end Wilson4DFeynmanKacTheorem

end YangMills 