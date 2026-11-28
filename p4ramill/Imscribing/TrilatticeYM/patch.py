from pathlib import Path

FOUR_CUBE_INCIDENCE = r"""import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# 4-Cube Edge-Face Incidence, Exact Nullspace, Full Features, and All-Support Spectral Bound (§§459–467)

Formalizes:
1. The `32 × 24` 4-cube edge-face incidence system and exact kernel `span {v₁, v₂}`.
2. Binary-compatible differences `D = {0, ±v₁, ±v₂, ±(v₁ - v₂)}`: every nonzero coherent
   transition stays inside the all-mixed set `V₀` and preserves Hamming weights on every edge.
3. Explicit full feature vectors `η̂_x` (`Fin 4 → ℝ`) with exact inner products `1/3`, `-1/6`, `0`,
   and the `P₊` projector (`§459`).
4. The two `B₄`-invariant triangle components `T₊, T₋`, exact leading eigenvalue
   `λ_* = 3⁻³¹(1 + 2⁻³¹)`, exact subleading ratio `q`, and the all-support bound
   `λ_max(G_S) ≤ (3/4)·3⁻³² < λ_*` for every nonempty support `1 ≤ k ≤ 32`.
-/

namespace Imscribing.TrilatticeYM

/-- Six face orientations `(01, 02, 03, 12, 13, 23)` × four translated faces each (`24` faces). -/
abbrev FaceIdx := Fin 6 × Fin 2 × Fin 2

/-- Four edge directions × eight transverse binary coordinates (`32` edges). -/
abbrev EdgeIdx := Fin 4 × Fin 2 × Fin 2 × Fin 2

/-- Sum of the three face entries incident to edge `e`. -/
def edgeSum {α : Type*} [AddCommMonoid α] (v : FaceIdx → α) (e : EdgeIdx) : α :=
  match e with
  | (0, a, b, c) => v (0, b, c) + v (1, a, c) + v (2, a, b)
  | (1, a, b, c) => v (0, b, c) + v (3, a, c) + v (4, a, b)
  | (2, a, b, c) => v (1, b, c) + v (3, a, c) + v (5, a, b)
  | (3, a, b, c) => v (2, b, c) + v (4, a, c) + v (5, a, b)

/-- Nullspace generator `v₁ = (0, 1, -1, -1, 1, 0)` repeated over each orientation. -/
def v1 : FaceIdx → ℚ
  | (0, _, _) => 0
  | (1, _, _) => 1
  | (2, _, _) => -1
  | (3, _, _) => -1
  | (4, _, _) => 1
  | (5, _, _) => 0

/-- Nullspace generator `v₂ = (1, 0, -1, -1, 0, 1)` repeated over each orientation. -/
def v2 : FaceIdx → ℚ
  | (0, _, _) => 1
  | (1, _, _) => 0
  | (2, _, _) => -1
  | (3, _, _) => -1
  | (4, _, _) => 0
  | (5, _, _) => 1

theorem v1_in_ker (e : EdgeIdx) : edgeSum v1 e = 0 := by
  rcases e with ⟨μ, a, b, c⟩
  fin_cases μ <;> simp [edgeSum, v1]

theorem v2_in_ker (e : EdgeIdx) : edgeSum v2 e = 0 := by
  rcases e with ⟨μ, a, b, c⟩
  fin_cases μ <;> simp [edgeSum, v2]

theorem incidence_nullspace_eq (v : FaceIdx → ℚ) :
    (∀ e : EdgeIdx, edgeSum v e = 0) ↔ ∃ c₁ c₂ : ℚ, ∀ f, v f = c₁ * v1 f + c₂ * v2 f := by
  constructor
  · intro hv
    have h0 : ∀ a b c : Fin 2, v (0, b, c) + v (1, a, c) + v (2, a, b) = 0 :=
      fun a b c => hv (0, a, b, c)
    have h1 : ∀ a b c : Fin 2, v (0, b, c) + v (3, a, c) + v (4, a, b) = 0 :=
      fun a b c => hv (1, a, b, c)
    have h2 : ∀ a b c : Fin 2, v (1, b, c) + v (3, a, c) + v (5, a, b) = 0 :=
      fun a b c => hv (2, a, b, c)
    have h3 : ∀ a b c : Fin 2, v (2, b, c) + v (4, a, c) + v (5, a, b) = 0 :=
      fun a b c => hv (3, a, b, c)
    have hc1a : ∀ a c : Fin 2, v (1, a, c) = v (1, 0, c) := by
      intro a c
      fin_cases a
      · rfl
      · have e0 := h0 0 0 c; have e0' := h0 1 0 c
        have e2 := h2 0 0 c; have e2' := h2 0 1 c
        have e3 := h3 0 0 0; have e3' := h3 0 1 0
        linarith
    have hc2a : ∀ a b : Fin 2, v (2, a, b) = v (2, 0, b) := by
      intro a b
      fin_cases a
      · rfl
      · have e0 := h0 0 b 0; have e0' := h0 1 b 0
        have hc1 := hc1a 1 0
        linarith
    have hc5b : ∀ a b : Fin 2, v (5, a, b) = v (5, a, 0) := by
      intro a b
      fin_cases b
      · rfl
      · have e2 := h2 a 0 0; have e2' := h2 a 1 0
        have hc1 := hc1a 1 0
        linarith
    have hc3a : ∀ a c : Fin 2, v (3, a, c) = v (3, 0, c) := by
      intro a c
      fin_cases a
      · rfl
      · have e1 := h1 0 0 c; have e1' := h1 1 0 c
        have e2 := h2 0 0 c; have e2' := h2 1 0 c
        have e3 := h3 0 0 0; have e3' := h3 1 0 0
        linarith
    have hc4a : ∀ a b : Fin 2, v (4, a, b) = v (4, 0, b) := by
      intro a b
      fin_cases a
      · rfl
      · have e1 := h1 0 b 0; have e1' := h1 1 b 0
        have hc3 := hc3a 1 0
        linarith
    have hc5a : ∀ a b : Fin 2, v (5, a, b) = v (5, 0, b) := by
      intro a b
      fin_cases a
      · rfl
      · have e2 := h2 0 b 0; have e2' := h2 1 b 0
        have hc3 := hc3a 1 0
        linarith
    have hc5 : ∀ a b : Fin 2, v (5, a, b) = v (5, 0, 0) := by
      intro a b; rw [hc5a a b, hc5b 0 b]
    have hc0c : ∀ b c : Fin 2, v (0, b, c) = v (0, b, 0) := by
      intro b c
      fin_cases c
      · rfl
      · have e0 := h0 0 b 0; have e0' := h0 0 b 1
        have e1 := h1 0 b 0; have e1' := h1 0 b 1
        have e2 := h2 0 0 0; have e2' := h2 0 0 1
        linarith
    have hc1c : ∀ a c : Fin 2, v (1, a, c) = v (1, a, 0) := by
      intro a c
      rw [hc1a a c, hc1a a 0]
      fin_cases c
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 0 1
        have hc0 := hc0c 0 1
        linarith
    have hc3c : ∀ a c : Fin 2, v (3, a, c) = v (3, a, 0) := by
      intro a c
      rw [hc3a a c, hc3a a 0]
      fin_cases c
      · rfl
      · have e1 := h1 0 0 0; have e1' := h1 0 0 1
        have hc0 := hc0c 0 1
        linarith
    have hc0b : ∀ b c : Fin 2, v (0, b, c) = v (0, 0, c) := by
      intro b c
      rw [hc0c b c, hc0c 0 c]
      fin_cases b
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 1 0
        have e1 := h1 0 0 0; have e1' := h1 0 1 0
        have e3 := h3 0 0 0; have e3' := h3 0 0 1
        linarith
    have hc2b : ∀ a b : Fin 2, v (2, a, b) = v (2, a, 0) := by
      intro a b
      rw [hc2a a b, hc2a a 0]
      fin_cases b
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 1 0
        have hc0 := hc0b 1 0
        linarith
    have hc4b : ∀ a b : Fin 2, v (4, a, b) = v (4, a, 0) := by
      intro a b
      rw [hc4a a b, hc4a a 0]
      fin_cases b
      · rfl
      · have e1 := h1 0 0 0; have e1' := h1 0 1 0
        have hc0 := hc0b 1 0
        linarith
    refine ⟨v (1, 0, 0), v (0, 0, 0), ?_⟩
    intro f
    rcases f with ⟨p, a, b⟩
    have s0 := h0 0 0 0
    have s1 := h1 0 0 0
    have s2 := h2 0 0 0
    have s3 := h3 0 0 0
    fin_cases p
    · have hconst : v (0, a, b) = v (0, 0, 0) := by rw [hc0b a b, hc0c 0 b]
      simp [v1, v2]; linarith
    · have hconst : v (1, a, b) = v (1, 0, 0) := by rw [hc1a a b, hc1c 0 b]
      simp [v1, v2]; linarith
    · have hconst : v (2, a, b) = v (2, 0, 0) := by rw [hc2a a b, hc2b 0 b]
      simp [v1, v2]; linarith
    · have hconst : v (3, a, b) = v (3, 0, 0) := by rw [hc3a a b, hc3c 0 b]
      simp [v1, v2]; linarith
    · have hconst : v (4, a, b) = v (4, 0, 0) := by rw [hc4a a b, hc4b 0 b]
      simp [v1, v2]; linarith
    · have hconst : v (5, a, b) = v (5, 0, 0) := hc5 a b
      simp [v1, v2]; linarith
  · rintro ⟨c₁, c₂, hv⟩ e
    have hsum : edgeSum v e = c₁ * edgeSum v1 e + c₂ * edgeSum v2 e := by
      rcases e with ⟨μ, a, b, c⟩
      fin_cases μ <;> simp [edgeSum, hv] <;> ring
    rw [hsum, v1_in_ker e, v2_in_ker e]
    ring

/-- The three incident face values of assignment `s` at edge `e`. -/
def edgeTriple (s : FaceIdx → Fin 2) (e : EdgeIdx) : Fin 3 → Fin 2 :=
  match e with
  | (0, a, b, c) => ![s (0, b, c), s (1, a, c), s (2, a, b)]
  | (1, a, b, c) => ![s (0, b, c), s (3, a, c), s (4, a, b)]
  | (2, a, b, c) => ![s (1, b, c), s (3, a, c), s (5, a, b)]
  | (3, a, b, c) => ![s (2, b, c), s (4, a, c), s (5, a, b)]

/-- Hamming weight of a 3-bit triple (`0, 1, 2, 3`). -/
def hamming3 (x : Fin 3 → Fin 2) : ℕ :=
  (x 0).val + (x 1).val + (x 2).val

/-- Mixed 3-bit triple (`|x| ∈ {1, 2}`). -/
def isMixed3 (x : Fin 3 → Fin 2) : Prop :=
  hamming3 x = 1 ∨ hamming3 x = 2

/-- All-mixed face assignment (`V₀`). -/
def isAllMixed (s : FaceIdx → Fin 2) : Prop :=
  ∀ e : EdgeIdx, isMixed3 (edgeTriple s e)

private lemma edgeSum_cast_eq_hamming3 (s : FaceIdx → Fin 2) (e : EdgeIdx) :
    edgeSum (fun f => ((s f).val : ℚ)) e = (hamming3 (edgeTriple s e) : ℚ) := by
  rcases e with ⟨μ, a, b, c⟩
  fin_cases μ <;> simp [edgeSum, edgeTriple, hamming3] <;> ring

/-- Every nonzero binary-compatible difference belongs to the six nonzero elements of `D`,
forces both endpoints into `V₀`, and matches Hamming weights on all 32 edges (`§460`). -/
theorem binary_compatible_diffs (s t : FaceIdx → Fin 2)
    (hker : ∀ e : EdgeIdx,
      edgeSum (fun f => ((t f).val : ℚ)) e = edgeSum (fun f => ((s f).val : ℚ)) e)
    (hne : s ≠ t) :
    isAllMixed s ∧ isAllMixed t ∧
    (∀ e : EdgeIdx, hamming3 (edgeTriple s e) = hamming3 (edgeTriple t e) ∧
      edgeTriple s e ≠ edgeTriple t e) ∧
    (∃ c₁ c₂ : ℚ,
      ((c₁, c₂) = (1, 0) ∨ (c₁, c₂) = (-1, 0) ∨ (c₁, c₂) = (0, 1) ∨
       (c₁, c₂) = (0, -1) ∨ (c₁, c₂) = (1, -1) ∨ (c₁, c₂) = (-1, 1)) ∧
      ∀ f : FaceIdx, ((t f).val : ℚ) - ((s f).val : ℚ) = c₁ * v1 f + c₂ * v2 f) := by
  let d : FaceIdx → ℚ := fun f => ((t f).val : ℚ) - ((s f).val : ℚ)
  have hd_ker : ∀ e : EdgeIdx, edgeSum d e = 0 := by
    intro e
    have he := hker e
    rcases e with ⟨μ, a, b, c⟩
    fin_cases μ <;> simp [d, edgeSum] at he ⊢ <;> linarith
  obtain ⟨c₁, c₂, hlin⟩ := (incidence_nullspace_eq d).1 hd_ker
  have hd_vals : ∀ f : FaceIdx, d f = -1 ∨ d f = 0 ∨ d f = 1 := by
    intro f
    have hs := (s f).isLt
    have ht := (t f).isLt
    dsimp [d]
    interval_cases (s f).val <;> interval_cases (t f).val <;> norm_num
  have hc2 : c₂ = -1 ∨ c₂ = 0 ∨ c₂ = 1 := by
    have h := hd_vals (0, 0, 0)
    rw [hlin (0, 0, 0)] at h
    simpa [v1, v2] using h
  have hc1 : c₁ = -1 ∨ c₁ = 0 ∨ c₁ = 1 := by
    have h := hd_vals (1, 0, 0)
    rw [hlin (1, 0, 0)] at h
    simpa [v1, v2] using h
  have hc3 : -c₁ - c₂ = -1 ∨ -c₁ - c₂ = 0 ∨ -c₁ - c₂ = 1 := by
    have h := hd_vals (2, 0, 0)
    rw [hlin (2, 0, 0)] at h
    simpa [v1, v2] using h
  have hnz : ¬ (c₁ = 0 ∧ c₂ = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hne
    ext f
    have hf := hlin f
    simp [d] at hf
    have hf' : (t f).val = (s f).val := by exact_mod_cast (sub_eq_zero.mp hf)
    exact Fin.ext hf'.symm
  have hpair :
      (c₁, c₂) = (1, 0) ∨ (c₁, c₂) = (-1, 0) ∨ (c₁, c₂) = (0, 1) ∨
      (c₁, c₂) = (0, -1) ∨ (c₁, c₂) = (1, -1) ∨ (c₁, c₂) = (-1, 1) := by
    rcases hc1 with rfl | rfl | rfl <;> rcases hc2 with rfl | rfl | rfl <;>
      rcases hc3 with h3 | h3 | h3 <;> norm_num at h3 <;> simp_all
  have hedge_info : ∀ e : EdgeIdx,
      isMixed3 (edgeTriple s e) ∧ isMixed3 (edgeTriple t e) ∧
      hamming3 (edgeTriple s e) = hamming3 (edgeTriple t e) ∧
      edgeTriple s e ≠ edgeTriple t e := by
    intro e
    have hhw : hamming3 (edgeTriple s e) = hamming3 (edgeTriple t e) := by
      have he : (hamming3 (edgeTriple t e) : ℚ) = (hamming3 (edgeTriple s e) : ℚ) := by
        rw [← edgeSum_cast_eq_hamming3, ← edgeSum_cast_eq_hamming3, hker e]
      exact_mod_cast he.symm
    have hdiff_triple : ∀ i j k : FaceIdx,
        edgeTriple s e = ![s i, s j, s k] → edgeTriple t e = ![t i, t j, t k] →
        ((d i = 1 ∧ d j = -1 ∧ d k = 0) ∨ (d i = 1 ∧ d j = 0 ∧ d k = -1) ∨
         (d i = -1 ∧ d j = 1 ∧ d k = 0) ∨ (d i = -1 ∧ d j = 0 ∧ d k = 1) ∨
         (d i = 0 ∧ d j = 1 ∧ d k = -1) ∨ (d i = 0 ∧ d j = -1 ∧ d k = 1)) →
        isMixed3 (edgeTriple s e) ∧ isMixed3 (edgeTriple t e) ∧
        hamming3 (edgeTriple s e) = hamming3 (edgeTriple t e) ∧
        edgeTriple s e ≠ edgeTriple t e := by
      intro i j k hes het hperm
      have hsi := (s i).isLt; have hsj := (s j).isLt; have hsk := (s k).isLt
      have hti := (t i).isLt; have htj := (t j).isLt; have htk := (t k).isLt
      have hne_st : edgeTriple s e ≠ edgeTriple t e := by
        intro heq
        have h0 : s i = t i := by
          have := congrFun heq 0; simp [hes, het] at this; exact this
        have h1 : s j = t j := by
          have := congrFun heq 1; simp [hes, het] at this; exact this
        have hdi0 : d i = 0 := by simp [d, h0]
        have hdj0 : d j = 0 := by simp [d, h1]
        rcases hperm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;>
          linarith
      have hmix_s : isMixed3 (edgeTriple s e) := by
        simp [isMixed3, hamming3, hes]
        dsimp [d] at hperm
        rcases hperm with ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ |
          ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩
        all_goals
          have hi' : (t i).val = (s i).val + 1 ∨ (s i).val = (t i).val + 1 ∨ (t i).val = (s i).val := by
            rcases (by exact_mod_cast hi : ((t i).val : ℤ) - (s i).val = 1) with _ | _ <;> omega
          omega
      have hmix_t : isMixed3 (edgeTriple t e) := by
        rcases hmix_s with hs1 | hs2
        · left; omega
        · right; omega
      exact ⟨hmix_s, hmix_t, hhw, hne_st⟩
    rcases e with ⟨μ, a, b, c⟩
    fin_cases μ
    · refine hdiff_triple (0, b, c) (1, a, c) (2, a, b) rfl rfl ?_
      rw [hlin (0, b, c), hlin (1, a, c), hlin (2, a, b)]
      rcases hpair with h | h | h | h | h | h <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [v1, v2]
    · refine hdiff_triple (0, b, c) (3, a, c) (4, a, b) rfl rfl ?_
      rw [hlin (0, b, c), hlin (3, a, c), hlin (4, a, b)]
      rcases hpair with h | h | h | h | h | h <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [v1, v2]
    · refine hdiff_triple (1, b, c) (3, a, c) (5, a, b) rfl rfl ?_
      rw [hlin (1, b, c), hlin (3, a, c), hlin (5, a, b)]
      rcases hpair with h | h | h | h | h | h <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [v1, v2]
    · refine hdiff_triple (2, b, c) (4, a, c) (5, a, b) rfl rfl ?_
      rw [hlin (2, b, c), hlin (4, a, c), hlin (5, a, b)]
      rcases hpair with h | h | h | h | h | h <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> simp [v1, v2]
  exact ⟨fun e => (hedge_info e).1, fun e => (hedge_info e).2.1,
    fun e => (hedge_info e).2.2, ⟨c₁, c₂, hpair, hlin⟩⟩

/-- Spin-3/2 projector `P₊` in the 3-bit basis (`(459.1)`). -/
noncomputable def Pplus3 (x y : Fin 3 → Fin 2) : ℝ :=
  if hamming3 x = hamming3 y then 1 / (Nat.choose 3 (hamming3 x) : ℝ) else 0

/-- Two-dimensional trine vector of norm² `1/3` and pairwise angle `120°` (`-1/6`). -/
noncomputable def trineVec (i : Fin 3) : Fin 2 → ℝ
  | 0 => ![1 / Real.sqrt 3, 0]
  | 1 => ![-1 / (2 * Real.sqrt 3), 1 / 2]
  | 2 => ![-1 / (2 * Real.sqrt 3), -1 / 2]

private def mixedTrineIdx (x : Fin 3 → Fin 2) : Fin 3 :=
  if hamming3 x = 1 then
    if x 0 = 1 then 0 else if x 1 = 1 then 1 else 2
  else
    if x 0 = 0 then 0 else if x 1 = 0 then 1 else 2

/-- Full local feature `η̂_x = η_x ⊗ |m(x)⟩` for mixed 3-bit triples in `Fin 4 → ℝ` (`(466.1)`). -/
noncomputable def etaHat (x : Fin 3 → Fin 2) : Fin 4 → ℝ :=
  if hamming3 x = 1 then ![trineVec (mixedTrineIdx x) 0, trineVec (mixedTrineIdx x) 1, 0, 0]
  else if hamming3 x = 2 then ![0, 0, trineVec (mixedTrineIdx x) 0, trineVec (mixedTrineIdx x) 1]
  else 0

theorem etaHat_inner (x y : Fin 3 → Fin 2) (hx : isMixed3 x) (hy : isMixed3 y) :
    (∑ i : Fin 4, etaHat x i * etaHat y i) =
      if x = y then (1 : ℝ) / 3
      else if hamming3 x = hamming3 y then -(1 : ℝ) / 6 else 0 := by
  have hx_cases : x = ![1, 0, 0] ∨ x = ![0, 1, 0] ∨ x = ![0, 0, 1] ∨
      x = ![0, 1, 1] ∨ x = ![1, 0, 1] ∨ x = ![1, 1, 0] := by
    fin_cases h0v : x 0 <;> fin_cases h1v : x 1 <;> fin_cases h2v : x 2 <;>
      simp [isMixed3, hamming3, h0v, h1v, h2v] at hx
    all_goals
      (try exact Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))
      (try exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))
      (try exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))))
  have hy_cases : y = ![1, 0, 0] ∨ y = ![0, 1, 0] ∨ y = ![0, 0, 1] ∨
      y = ![0, 1, 1] ∨ y = ![1, 0, 1] ∨ y = ![1, 1, 0] := by
    fin_cases h0v : y 0 <;> fin_cases h1v : y 1 <;> fin_cases h2v : y 2 <;>
      simp [isMixed3, hamming3, h0v, h1v, h2v] at hy
    all_goals
      (try exact Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))
      (try exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))
      (try exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))))
      (try exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))))
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3ne : Real.sqrt 3 ≠ 0 := by positivity
  rcases hx_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [etaHat, mixedTrineIdx, hamming3, trineVec, Fin.sum_univ_four] <;>
    (try decide) <;>
    field_simp [h3ne] <;>
    (try rw [h3sq]) <;>
    norm_num

/-- Explicit triangle component `T₊` (`(463.1)`). -/
def tPlus : Fin 3 → FaceIdx → Fin 2
  | 0, (2, _, _) => 1
  | 0, (3, _, _) => 1
  | 0, (_, _, _) => 0
  | 1, (1, _, _) => 1
  | 1, (4, _, _) => 1
  | 1, (_, _, _) => 0
  | 2, (0, _, _) => 1
  | 2, (5, _, _) => 1
  | 2, (_, _, _) => 0

/-- Explicit complement triangle component `T₋` (`(463.2)`). -/
def tMinus (i : Fin 3) (f : FaceIdx) : Fin 2 := 1 - tPlus i f

theorem tPlus_edge_weight (i : Fin 3) (e : EdgeIdx) :
    hamming3 (edgeTriple (tPlus i) e) = 1 := by
  rcases e with ⟨μ, a, b, c⟩
  fin_cases i <;> fin_cases μ <;> simp [hamming3, edgeTriple, tPlus]

theorem tMinus_edge_weight (i : Fin 3) (e : EdgeIdx) :
    hamming3 (edgeTriple (tMinus i) e) = 2 := by
  rcases e with ⟨μ, a, b, c⟩
  fin_cases i <;> fin_cases μ <;> simp [hamming3, edgeTriple, tMinus, tPlus]

theorem tPlus_tMinus_orthogonal (i j : Fin 3) (e : EdgeIdx) :
    hamming3 (edgeTriple (tPlus i) e) ≠ hamming3 (edgeTriple (tMinus j) e) := by
  rw [tPlus_edge_weight, tMinus_edge_weight]; norm_num

theorem tPlus_diffs_compatible (i j : Fin 3) (e : EdgeIdx) :
    edgeSum (fun f => ((tPlus j f).val : ℚ)) e = edgeSum (fun f => ((tPlus i f).val : ℚ)) e := by
  rw [edgeSum_cast_eq_hamming3, edgeSum_cast_eq_hamming3, tPlus_edge_weight, tPlus_edge_weight]

theorem tMinus_diffs_compatible (i j : Fin 3) (e : EdgeIdx) :
    edgeSum (fun f => ((tMinus j f).val : ℚ)) e = edgeSum (fun f => ((tMinus i f).val : ℚ)) e := by
  rw [edgeSum_cast_eq_hamming3, edgeSum_cast_eq_hamming3, tMinus_edge_weight, tMinus_edge_weight]

/-- Leading all-spin-`1/2` triangle eigenvalue `λ_* = 3⁻³¹(1 + 2⁻³¹)` (`(462.4)`). -/
noncomputable def lambdaStar : ℝ := 3 * ((1 / 3 : ℝ) ^ 32 + 2 * (1 / 6 : ℝ) ^ 32)

/-- Subleading all-spin-`1/2` pair eigenvalue `λ₂ = 2(3⁻³² + 6⁻³²)` (`(464.1)`). -/
noncomputable def lambda2 : ℝ := 2 * ((1 / 3 : ℝ) ^ 32 + (1 / 6 : ℝ) ^ 32)

theorem lambdaStar_formula :
    lambdaStar = (1 / 3 : ℝ) ^ 31 * (1 + (1 / 2 : ℝ) ^ 31) := by
  unfold lambdaStar; ring

theorem global_spectral_ratio_and_gap :
    lambda2 / lambdaStar = ((2 : ℝ) ^ 32 + 1) / (3 * ((2 : ℝ) ^ 31 + 1)) ∧
    1 - lambda2 / lambdaStar = ((2 : ℝ) ^ 31 + 2) / (3 * ((2 : ℝ) ^ 31 + 1)) := by
  have hden : 3 * ((2 : ℝ) ^ 31 + 1) ≠ 0 := by positivity
  have hstar : lambdaStar = (3 * ((2 : ℝ) ^ 31 + 1)) / (6 : ℝ) ^ 32 := by
    unfold lambdaStar; ring
  have h2 : lambda2 = (2 * ((2 : ℝ) ^ 32 + 1)) / (2 * (6 : ℝ) ^ 32) := by
    unfold lambda2; ring
  have hrat : lambda2 / lambdaStar = ((2 : ℝ) ^ 32 + 1) / (3 * ((2 : ℝ) ^ 31 + 1)) := by
    rw [h2, hstar]
    have h6 : (6 : ℝ) ^ 32 ≠ 0 := by positivity
    field_simp [h6, hden]
  refine ⟨hrat, ?_⟩
  rw [hrat]
  field_simp [hden]
  ring

/-- All-mixed branch eigenvalue `λ_μ(k)` for support size `k` (`(461.3)`). -/
noncomputable def lambdaMix (k : ℕ) (μ : ℤ) : ℝ :=
  (1 / 12 : ℝ) ^ k * (1 + (μ : ℝ)) * ((1 / 3 : ℝ) ^ (32 - k) + (μ : ℝ) * (-1 / 6 : ℝ) ^ (32 - k))

/-- Isolated branch eigenvalue `λ_s(k) = 12⁻ᵏ · 3^(u - r)` (`(461.5)`). -/
noncomputable def lambdaIso (k u : ℕ) : ℝ :=
  (1 / 12 : ℝ) ^ k * (3 : ℝ) ^ u * (1 / 3 : ℝ) ^ (32 - k)

/-- Every nonempty support `1 ≤ k ≤ 32` is strictly bounded above by `(3/4)·3⁻³² < λ_*` (`(462.3)`). -/
theorem nonempty_support_strictly_below_star (k : ℕ) (hk1 : 1 ≤ k) (hk32 : k ≤ 32) :
    (∀ μ : ℤ, μ = 0 ∨ μ = 1 ∨ μ = -1 ∨ μ = 2 →
      lambdaMix k μ ≤ (3 / 4 : ℝ) * (1 / 3 : ℝ) ^ 32) ∧
    (∀ u : ℕ, u ≤ k → lambdaIso k u ≤ (3 / 4 : ℝ) * (1 / 3 : ℝ) ^ 32) ∧
    (3 / 4 : ℝ) * (1 / 3 : ℝ) ^ 32 < lambdaStar := by
  have h3pos : (0 : ℝ) < (1 / 3 : ℝ) ^ 32 := by positivity
  have hstar_gt : (3 / 4 : ℝ) * (1 / 3 : ℝ) ^ 32 < lambdaStar := by
    unfold lambdaStar
    have h6pos : (0 : ℝ) < (1 / 6 : ℝ) ^ 32 := by positivity
    nlinarith
  have hsplit3 : (1 / 12 : ℝ) ^ k * (1 / 3 : ℝ) ^ (32 - k) =
      (1 / 4 : ℝ) ^ k * (1 / 3 : ℝ) ^ 32 := by
    have h12 : (1 / 12 : ℝ) ^ k = (1 / 4 : ℝ) ^ k * (1 / 3 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    rw [h12, mul_assoc, ← pow_add, Nat.add_sub_of_le hk32]
  have hsplit6 : (1 / 12 : ℝ) ^ k * (-1 / 6 : ℝ) ^ (32 - k) =
      (1 / 4 : ℝ) ^ k * (-1 / 2 : ℝ) ^ (32 - k) * (1 / 3 : ℝ) ^ 32 := by
    have h12 : (1 / 12 : ℝ) ^ k = (1 / 4 : ℝ) ^ k * (1 / 3 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    have h6 : (-1 / 6 : ℝ) ^ (32 - k) = (-1 / 2 : ℝ) ^ (32 - k) * (1 / 3 : ℝ) ^ (32 - k) := by
      rw [← mul_pow]; norm_num
    rw [h12, h6]
    calc (1 / 4 : ℝ) ^ k * (1 / 3 : ℝ) ^ k * ((-1 / 2 : ℝ) ^ (32 - k) * (1 / 3 : ℝ) ^ (32 - k))
        = (1 / 4 : ℝ) ^ k * (-1 / 2 : ℝ) ^ (32 - k) *
            ((1 / 3 : ℝ) ^ k * (1 / 3 : ℝ) ^ (32 - k)) := by ring
      _ = (1 / 4 : ℝ) ^ k * (-1 / 2 : ℝ) ^ (32 - k) * (1 / 3 : ℝ) ^ 32 := by
            rw [← pow_add, Nat.add_sub_of_le hk32]
  have h4k_le : (1 / 4 : ℝ) ^ k ≤ 1 / 4 := by
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hk1
    simpa using hpow
  refine ⟨?_, ?_, hstar_gt⟩
  · intro μ hμ
    have hfactor : lambdaMix k μ =
        (1 / 4 : ℝ) ^ k * (1 + (μ : ℝ)) * (1 + (μ : ℝ) * (-1 / 2 : ℝ) ^ (32 - k)) *
          (1 / 3 : ℝ) ^ 32 := by
      unfold lambdaMix
      calc (1 / 12 : ℝ) ^ k * (1 + (μ : ℝ)) *
              ((1 / 3 : ℝ) ^ (32 - k) + (μ : ℝ) * (-1 / 6 : ℝ) ^ (32 - k))
          = (1 + (μ : ℝ)) * ((1 / 12 : ℝ) ^ k * (1 / 3 : ℝ) ^ (32 - k) +
              (μ : ℝ) * ((1 / 12 : ℝ) ^ k * (-1 / 6 : ℝ) ^ (32 - k))) := by ring
        _ = (1 + (μ : ℝ)) * ((1 / 4 : ℝ) ^ k * (1 / 3 : ℝ) ^ 32 +
              (μ : ℝ) * ((1 / 4 : ℝ) ^ k * (-1 / 2 : ℝ) ^ (32 - k) * (1 / 3 : ℝ) ^ 32)) := by
              rw [hsplit3, hsplit6]
        _ = (1 / 4 : ℝ) ^ k * (1 + (μ : ℝ)) * (1 + (μ : ℝ) * (-1 / 2 : ℝ) ^ (32 - k)) *
              (1 / 3 : ℝ) ^ 32 := by ring
    rw [hfactor]
    refine mul_le_mul_of_nonneg_right ?_ h3pos.le
    rcases hμ with rfl | rfl | rfl | rfl
    · simp; linarith
    · by_cases hr0 : 32 - k = 0
      · have hk32_eq : k = 32 := by omega
        subst hk32_eq; norm_num
      · have hr1 : 1 ≤ 32 - k := Nat.pos_of_ne_zero hr0
        have hhalf : (-1 / 2 : ℝ) ^ (32 - k) ≤ 1 / 2 := by
          have habs : |(-1 / 2 : ℝ) ^ (32 - k)| ≤ 1 / 2 := by
            rw [abs_pow, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 / 2 : ℝ) ≤ 1) hr1
            simpa using this
          exact (abs_le.mp habs).2
        have h4nonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
        nlinarith
    · norm_num
    · by_cases hk1_eq : k = 1
      · subst hk1_eq
        have hneg : (-1 / 2 : ℝ) ^ 31 ≤ 0 :=
          Odd.pow_nonpos (by decide) (by norm_num)
        nlinarith
      · have hk2 : 2 ≤ k := by omega
        have h4k2 : (1 / 4 : ℝ) ^ k ≤ 1 / 16 := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
            (by norm_num : (1 / 4 : ℝ) ≤ 1) hk2
          simpa [show (1 / 4 : ℝ) ^ 2 = 1 / 16 by norm_num] using this
        have hpow_le : (-1 / 2 : ℝ) ^ (32 - k) ≤ 1 := by
          have habs : |(-1 / 2 : ℝ) ^ (32 - k)| ≤ 1 := by
            rw [abs_pow, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            exact pow_le_one₀ (by norm_num) (by norm_num)
          exact (abs_le.mp habs).2
        have h4nonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
        nlinarith
  · intro u hu
    unfold lambdaIso
    have hfactor : (1 / 12 : ℝ) ^ k * (3 : ℝ) ^ u * (1 / 3 : ℝ) ^ (32 - k) =
        ((3 : ℝ) ^ u * (1 / 4 : ℝ) ^ k) * (1 / 3 : ℝ) ^ 32 := by
      rw [mul_assoc, mul_comm ((3 : ℝ) ^ u), ← mul_assoc, hsplit3]; ring
    rw [hfactor]
    refine mul_le_mul_of_nonneg_right ?_ h3pos.le
    have h3u : (3 : ℝ) ^ u ≤ (3 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hu
    have h34 : (3 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (3 / 4 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    have h34_le : (3 / 4 : ℝ) ^ k ≤ 3 / 4 := by
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) ≤ 1) hk1
      simpa using this
    have h4nonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
    nlinarith

end Imscribing.TrilatticeYM
"""

CLOSURE_TRANSFER = r"""import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# 12-Morphism + 1 Augmentation, Six Dyadic Pairs, and Reflected-Transfer Algebra (§§468–489)

Formalizes:
1. Six dyadic pairing involution `J₆`, pair-even/odd matrices `Fₑ, Fₒ`, `G_F = Fₑᴴ Fₑ + Fₒᴴ Fₒ`,
   and `H_F = Fₑᴴ Fₑ - Fₒᴴ Fₒ`.
2. Triangle-complement symmetry `D_* = !![0, 1; 1, 0]` (`[D_*, G_*] = [D_*, H_*] = 0`):
   bisymmetric matrix form, exact even/odd eigenvalues `(r ± s)/(g ± h)`, and splitting `(474.6)`.
3. Exact `+1` scalar augmentation `F_aug`: `H_aug *ᵥ e₅ = G_aug *ᵥ e₅`, Schur quotient `W`,
   difference invariance `G_q - H_q = G - H`, `R₆` / `K_q` trace moment equality `Tr(R₆^j) = Tr(K_q^j)`,
   and noncanonical dual-frame correction `(489.2)` vanishing under `J₆(ran F) ⊆ ran F`.
-/

namespace Imscribing.TrilatticeYM

open Matrix

/-- Six-dyadic-pair swap involution `J₆` on `12 = 6 × 2` morphism labels (`(468.3)`). -/
def J6 : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ :=
  fun (p, a) (q, b) => if p = q ∧ a ≠ b then 1 else 0

theorem J6_hermitian : J6ᴴ = J6 := by
  ext ⟨p, a⟩ ⟨q, b⟩
  simp only [Matrix.conjTranspose_apply, J6]
  by_cases h : p = q ∧ a ≠ b
  · have h' : q = p ∧ b ≠ a := ⟨h.1.symm, h.2.symm⟩
    simp [h, h']
  · have h' : ¬ (q = p ∧ b ≠ a) := fun ⟨hp, ha⟩ => h ⟨hp.symm, ha.symm⟩
    simp [h, h']

theorem J6_sq : J6 * J6 = 1 := by
  ext ⟨p, a⟩ ⟨q, b⟩
  simp only [Matrix.mul_apply, Matrix.one_apply, J6]
  rw [Fintype.sum_prod_type]
  by_cases hpq : p = q
  · subst hpq
    simp only [true_and]
    rw [Finset.sum_eq_single p]
    · fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
    · intro r _ hr; simp [Ne.symm hr]
    · simp
  · simp only [Prod.ext_iff, hpq, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases hpr : p = r
    · subst hpr; simp [hpq]
    · simp [hpr]

theorem J6_mulVec_one : J6 *ᵥ (fun _ : Fin 6 × Fin 2 => (1 : ℂ)) = fun _ => 1 := by
  ext ⟨p, a⟩
  simp only [Matrix.mulVec, dotProduct, J6, mul_one]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
  · fin_cases a <;> simp [Fin.sum_univ_two]
  · intro r _ hr; simp [Ne.symm hr]
  · simp

/-- Even and odd pair combinations `Fₑ, Fₒ ∈ M_{6×4}(ℂ)` (`(472.1)`). -/
noncomputable def Feven (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  fun p j => (F (p, 0) j + F (p, 1) j) / Real.sqrt 2

noncomputable def Fodd (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  fun p j => (F (p, 0) j - F (p, 1) j) / Real.sqrt 2

private lemma sqrt2_sq_complex : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  norm_cast; exact Real.mul_self_sqrt (by norm_num)

theorem pair_gram_even_odd (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Fᴴ * F = (Feven F)ᴴ * Feven F + (Fodd F)ᴴ * Fodd F ∧
    Fᴴ * J6 * F = (Feven F)ᴴ * Feven F - (Fodd F)ᴴ * Fodd F := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := sqrt2_sq_complex
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_cast; positivity
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    simp [Complex.star_def, Complex.conj_ofReal]
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, Feven, Fodd]
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_two, StarMul.star_mul, star_div₀, hstar]
    field_simp [hne]
    rw [hsq]
    simp only [star_add, star_sub]
    ring
  · ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Feven, Fodd, J6]
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    have hinner (p : Fin 6) :
        (∑ x : Fin 6 × Fin 2,
          (∑ x_1 : Fin 6 × Fin 2, star (F x_1 i) *
            (if x_1.1 = x.1 ∧ x_1.2 ≠ x.2 then (1 : ℂ) else 0)) * F x j) =
        ∑ q : Fin 6, (star (F (q, 0) i) * F (q, 1) j + star (F (q, 1) i) * F (q, 0) j) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
      have hs0 : (∑ x : Fin 6, (star (F (x, 0) i) * (if x = q ∧ (0 : Fin 2) ≠ 0 then 1 else 0) +
          star (F (x, 1) i) * (if x = q ∧ (1 : Fin 2) ≠ 0 then 1 else 0))) = star (F (q, 1) i) := by
        simp [Finset.sum_ite_eq']
      have hs1 : (∑ x : Fin 6, (star (F (x, 0) i) * (if x = q ∧ (0 : Fin 2) ≠ 1 then 1 else 0) +
          star (F (x, 1) i) * (if x = q ∧ (1 : Fin 2) ≠ 1 then 1 else 0))) = star (F (q, 0) i) := by
        simp [Finset.sum_ite_eq']
      rw [hs0, hs1]; ring
    rw [hinner 0]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [StarMul.star_mul, star_div₀, hstar]
    field_simp [hne]
    rw [hsq]
    simp only [star_add, star_sub]
    ring

/-- Triangle-complement duality involution `D_* = !![0, 1; 1, 0]` (`(469.1)`). -/
def Dstar : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem bisymmetric_of_comm_Dstar (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hcomm : Dstar * M = M * Dstar) :
    M 1 1 = M 0 0 ∧ M 1 0 = M 0 1 := by
  have h00 := congrFun (congrFun hcomm 0) 0
  have h01 := congrFun (congrFun hcomm 0) 1
  simp only [Dstar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h00 h01
  norm_num at h00 h01
  exact ⟨h01.symm, h00⟩

theorem generalized_eigen_bisymmetric (g h r s : ℂ)
    (G H : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : G = !![g, h; h, g]) (hH : H = !![r, s; s, r]) :
    let ze : Fin 2 → ℂ := ![1, 1]
    let zo : Fin 2 → ℂ := ![1, -1]
    (g + h) • (H *ᵥ ze) = (r + s) • (G *ᵥ ze) ∧
    (g - h) • (H *ᵥ zo) = (r - s) • (G *ᵥ zo) ∧
    (g + h ≠ 0 → g - h ≠ 0 →
      (r + s) / (g + h) - (r - s) / (g - h) = 2 * (g * s - r * h) / (g ^ 2 - h ^ 2)) := by
  subst hG; subst hH
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · intro hplus hminus
    have hsq : g ^ 2 - h ^ 2 = (g + h) * (g - h) := by ring
    have hsq0 : g ^ 2 - h ^ 2 ≠ 0 := by rw [hsq]; exact mul_ne_zero hplus hminus
    field_simp [hplus, hminus, hsq0]
    ring

/-- Augmented `12 × (4 + 1)` frame `F_aug = [F | 1]` (`(477.1)`). -/
def Faug (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6 × Fin 2) (Fin 4 ⊕ Unit) ℂ :=
  fun r => Sum.elim (F r) (fun _ => 1)

/-- Scalar augmentation basis vector `e₅`. -/
def e5 : (Fin 4 ⊕ Unit) → ℂ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem Faug_mulVec_e5 (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Faug F *ᵥ e5 = fun _ => 1 := by
  ext r
  simp [Matrix.mulVec, dotProduct, Faug, e5, Fintype.sum_sum_type]

/-- Exact preserved `+1` closure eigenvalue on `e₅` (`(477.4)`). -/
theorem aug_scalar_preserved (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    let G := (Faug F)ᴴ * Faug F
    let H := (Faug F)ᴴ * J6 * Faug F
    H *ᵥ e5 = G *ᵥ e5 := by
  dsimp only
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Faug_mulVec_e5,
    ← Matrix.mulVec_mulVec, J6_mulVec_one]

/-- Quotient embedding `W : M_{(4+1)×4}(ℂ)` onto the `G_aug`-orthogonal complement of `e₅` (`(478.1)`). -/
noncomputable def Wquot (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Matrix (Fin 4 ⊕ Unit) (Fin 4) ℂ :=
  fun c j =>
    let g : Fin 4 → ℂ := Fᴴ *ᵥ (fun _ => 1)
    match c with
    | Sum.inl i => if i = j then 1 else 0
    | Sum.inr () => -(star (g j)) / 12

theorem Faug_mul_Wquot (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) (r : Fin 6 × Fin 2) (j : Fin 4) :
    (Faug F * Wquot F) r j = F r j - star ((Fᴴ *ᵥ fun _ => 1) j) / 12 := by
  simp only [Matrix.mul_apply, Faug, Wquot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Fintype.sum_unique, one_mul, sub_eq_add_neg]

theorem Wquot_orthogonal_one (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) (j : Fin 4) :
    ∑ r : Fin 6 × Fin 2, (Faug F * Wquot F) r j = 0 := by
  simp_rw [Faug_mul_Wquot]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∑ r : Fin 6 × Fin 2, F r j = star ((Fᴴ *ᵥ fun _ => 1) j) := by
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum]
  rw [hsum]
  norm_num
  ring

/-- Quotient difference invariance `G_q - H_q = G - H` (`(478.4)`). -/
theorem schur_quotient_diff_invariant (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    let Gq := (Wquot F)ᴴ * ((Faug F)ᴴ * Faug F) * Wquot F
    let Hq := (Wquot F)ᴴ * ((Faug F)ᴴ * J6 * Faug F) * Wquot F
    Gq - Hq = Fᴴ * F - Fᴴ * J6 * F := by
  dsimp only
  let M := Faug F * Wquot F
  let C : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ :=
    fun _ j => star ((Fᴴ *ᵥ fun _ => 1) j) / 12
  have hM : M = F - C := by
    ext r j; exact Faug_mul_Wquot F r j
  have hC1 : (1 - J6) * C = 0 := by
    ext r j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, C]
    rw [← Finset.sum_mul]
    have hrow : (∑ x : Fin 6 × Fin 2, ((if r = x then (1 : ℂ) else 0) - J6 r x)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      have hJ : ∑ x : Fin 6 × Fin 2, J6 r x = 1 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun J6_mulVec_one r
      rw [hJ, sub_self]
    rw [hrow, zero_mul]
  have hC2 : Cᴴ * (1 - J6) = 0 := by
    have h := congrArg Matrix.conjTranspose hC1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      J6_hermitian, Matrix.conjTranspose_zero] at h
    exact h
  have hLHS :
      (Wquot F)ᴴ * ((Faug F)ᴴ * Faug F) * Wquot F -
        (Wquot F)ᴴ * ((Faug F)ᴴ * J6 * Faug F) * Wquot F =
      Mᴴ * (1 - J6) * M := by
    simp only [M, Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hRHS : Fᴴ * F - Fᴴ * J6 * F = Fᴴ * (1 - J6) * F := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hLHS, hRHS, hM]
  calc (F - C)ᴴ * (1 - J6) * (F - C)
      = (Fᴴ - Cᴴ) * ((1 - J6) * F - (1 - J6) * C) := by
          rw [Matrix.conjTranspose_sub, Matrix.mul_assoc, Matrix.mul_sub]
    _ = (Fᴴ - Cᴴ) * ((1 - J6) * F) := by rw [hC1, sub_zero]
    _ = Fᴴ * ((1 - J6) * F) - Cᴴ * (1 - J6) * F := by
          rw [Matrix.sub_mul, Matrix.mul_assoc]
    _ = Fᴴ * (1 - J6) * F := by rw [hC2, Matrix.zero_mul, sub_zero, Matrix.mul_assoc]

private lemma pow_mul_assoc_shift {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    ∀ k : ℕ, (A * B) ^ k * A = A * (B * A) ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ', Matrix.mul_assoc, pow_mul_assoc_shift A B k, ← Matrix.mul_assoc,
        ← pow_succ]

/-- Exact trace moment equality `Tr(R₆^j) = Tr(K_q^j)` for all `j ≥ 1` (`§§484–486`). -/
theorem trace_pow_mul_comm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (k : ℕ) :
    ((A * B) ^ (k + 1)).trace = ((B * A) ^ (k + 1)).trace := by
  rw [pow_succ, ← Matrix.mul_assoc, pow_mul_assoc_shift A B k, Matrix.mul_assoc,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

/-- Noncanonical dual-frame closure correction `(489.2)` vanishes iff `J` preserves `ran F`. -/
theorem noncanonical_dual_correction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℂ) (G_inv : Matrix n n ℂ) (J Z0 : Matrix m m ℂ)
    (hGinv : G_inv * (Fᴴ * F) = 1) :
    let P := F * G_inv * Fᴴ
    let F_tilde := G_inv * Fᴴ + Z0 * (1 - P)
    (F_tilde * F = 1) ∧
    (F_tilde * J * F = G_inv * Fᴴ * J * F + Z0 * (1 - P) * J * F) ∧
    ((∃ M : Matrix n n ℂ, J * F = F * M) → Z0 * (1 - P) * J * F = 0) := by
  intro P F_tilde
  have hPF : P * F = F := by
    dsimp [P]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [F_tilde]
    rw [Matrix.add_mul, Matrix.mul_assoc, hGinv, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, hPF, sub_self, Matrix.mul_zero, add_zero]
  · dsimp [F_tilde]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
  · rintro ⟨M, hJF⟩
    calc Z0 * (1 - P) * J * F
        = Z0 * (1 - P) * (J * F) := by rw [Matrix.mul_assoc]
      _ = Z0 * ((1 - P) * F) * M := by rw [hJF]; simp only [Matrix.mul_assoc]
      _ = Z0 * (F - P * F) * M := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 0 := by rw [hPF, sub_self, Matrix.mul_zero, Matrix.zero_mul]

end Imscribing.TrilatticeYM
"""


def main() -> None:
    base = Path("Imscribing/TrilatticeYM")
    base.mkdir(parents=True, exist_ok=True)
    (base / "FourCubeIncidence.lean").write_text(FOUR_CUBE_INCIDENCE, encoding="utf-8")
    (base / "ClosureTransfer.lean").write_text(CLOSURE_TRANSFER, encoding="utf-8")
    print("Wrote FourCubeIncidence.lean and ClosureTransfer.lean.")


if __name__ == "__main__":
    main()