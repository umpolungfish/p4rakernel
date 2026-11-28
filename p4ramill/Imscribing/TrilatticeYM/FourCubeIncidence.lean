import Mathlib.Data.Matrix.Basic
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

private lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨n, hn⟩
  interval_cases n <;> simp [Fin.ext_iff]

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
      rcases fin2_cases a with rfl | rfl
      · rfl
      · have e0 := h0 0 0 c; have e0' := h0 1 0 c
        have e2 := h2 0 0 c; have e2' := h2 0 1 c
        have e3 := h3 0 0 0; have e3' := h3 0 1 0
        linarith
    have hc2a : ∀ a b : Fin 2, v (2, a, b) = v (2, 0, b) := by
      intro a b
      rcases fin2_cases a with rfl | rfl
      · rfl
      · have e0 := h0 0 b 0; have e0' := h0 1 b 0
        have hc1 := hc1a 1 0
        linarith
    have hc5b : ∀ a b : Fin 2, v (5, a, b) = v (5, a, 0) := by
      intro a b
      rcases fin2_cases b with rfl | rfl
      · rfl
      · have e2 := h2 a 0 0; have e2' := h2 a 1 0
        have hc1 := hc1a 1 0
        linarith
    have hc3a : ∀ a c : Fin 2, v (3, a, c) = v (3, 0, c) := by
      intro a c
      rcases fin2_cases a with rfl | rfl
      · rfl
      · have e1 := h1 0 0 c; have e1' := h1 1 0 c
        have e2 := h2 0 0 c; have e2' := h2 1 0 c
        have e3 := h3 0 0 0; have e3' := h3 1 0 0
        linarith
    have hc4a : ∀ a b : Fin 2, v (4, a, b) = v (4, 0, b) := by
      intro a b
      rcases fin2_cases a with rfl | rfl
      · rfl
      · have e1 := h1 0 b 0; have e1' := h1 1 b 0
        have hc3 := hc3a 1 0
        linarith
    have hc5a : ∀ a b : Fin 2, v (5, a, b) = v (5, 0, b) := by
      intro a b
      rcases fin2_cases a with rfl | rfl
      · rfl
      · have e2 := h2 0 b 0; have e2' := h2 1 b 0
        have hc3 := hc3a 1 0
        linarith
    have hc5 : ∀ a b : Fin 2, v (5, a, b) = v (5, 0, 0) := by
      intro a b; rw [hc5a a b, hc5b 0 b]
    have hc0c : ∀ b c : Fin 2, v (0, b, c) = v (0, b, 0) := by
      intro b c
      rcases fin2_cases c with rfl | rfl
      · rfl
      · have e0 := h0 0 b 0; have e0' := h0 0 b 1
        have e1 := h1 0 b 0; have e1' := h1 0 b 1
        have e2 := h2 0 0 0; have e2' := h2 0 0 1
        linarith
    have hc1c : ∀ a c : Fin 2, v (1, a, c) = v (1, a, 0) := by
      intro a c
      rw [hc1a a c, hc1a a 0]
      rcases fin2_cases c with rfl | rfl
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 0 1
        have hc0 := hc0c 0 1
        linarith
    have hc3c : ∀ a c : Fin 2, v (3, a, c) = v (3, a, 0) := by
      intro a c
      rw [hc3a a c, hc3a a 0]
      rcases fin2_cases c with rfl | rfl
      · rfl
      · have e1 := h1 0 0 0; have e1' := h1 0 0 1
        have hc0 := hc0c 0 1
        linarith
    have hc0b : ∀ b c : Fin 2, v (0, b, c) = v (0, 0, c) := by
      intro b c
      rw [hc0c b c, hc0c 0 c]
      rcases fin2_cases b with rfl | rfl
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 1 0
        have e1 := h1 0 0 0; have e1' := h1 0 1 0
        have e3 := h3 0 0 0; have e3' := h3 0 0 1
        linarith
    have hc2b : ∀ a b : Fin 2, v (2, a, b) = v (2, a, 0) := by
      intro a b
      rw [hc2a a b, hc2a a 0]
      rcases fin2_cases b with rfl | rfl
      · rfl
      · have e0 := h0 0 0 0; have e0' := h0 0 1 0
        have hc0 := hc0b 1 0
        linarith
    have hc4b : ∀ a b : Fin 2, v (4, a, b) = v (4, a, 0) := by
      intro a b
      rw [hc4a a b, hc4a a 0]
      rcases fin2_cases b with rfl | rfl
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

private lemma fin2_diff_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = 1) :
    a.val = 0 ∧ b.val = 1 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    (try norm_num at h) <;> norm_num

private lemma fin2_diff_neg_one {a b : Fin 2} (h : (b.val : ℚ) - (a.val : ℚ) = -1) :
    a.val = 1 ∧ b.val = 0 := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    (try norm_num at h) <;> norm_num

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
  have hc3 : -c₁ + -c₂ = -1 ∨ -c₁ + -c₂ = 0 ∨ -c₁ + -c₂ = 1 := by
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
    exact hf'.symm
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
        rcases hperm with ⟨hi, hj, _⟩ | ⟨hi, _, hk⟩ | ⟨hi, hj, _⟩ |
          ⟨hi, _, hk⟩ | ⟨_, hj, hk⟩ | ⟨_, hj, hk⟩
        · obtain ⟨ha, _⟩ := fin2_diff_one hi; obtain ⟨hb, _⟩ := fin2_diff_neg_one hj
          omega
        · obtain ⟨ha, _⟩ := fin2_diff_one hi; obtain ⟨hc, _⟩ := fin2_diff_neg_one hk
          omega
        · obtain ⟨ha, _⟩ := fin2_diff_neg_one hi; obtain ⟨hb, _⟩ := fin2_diff_one hj
          omega
        · obtain ⟨ha, _⟩ := fin2_diff_neg_one hi; obtain ⟨hc, _⟩ := fin2_diff_one hk
          omega
        · obtain ⟨hb, _⟩ := fin2_diff_one hj; obtain ⟨hc, _⟩ := fin2_diff_neg_one hk
          omega
        · obtain ⟨hb, _⟩ := fin2_diff_neg_one hj; obtain ⟨hc, _⟩ := fin2_diff_one hk
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
noncomputable def trineVec : Fin 3 → Fin 2 → ℝ
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

private lemma mixed3_cases (x : Fin 3 → Fin 2) (hx : isMixed3 x) :
    x = ![1, 0, 0] ∨ x = ![0, 1, 0] ∨ x = ![0, 0, 1] ∨
    x = ![0, 1, 1] ∨ x = ![1, 0, 1] ∨ x = ![1, 1, 0] := by
  rcases fin2_cases (x 0) with h0v | h0v <;>
    rcases fin2_cases (x 1) with h1v | h1v <;>
    rcases fin2_cases (x 2) with h2v | h2v <;>
    simp [isMixed3, hamming3, h0v, h1v, h2v] at hx
  · exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))
  · exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v]))))
  · exact Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext i; fin_cases i <;> simp [h0v, h1v, h2v])))))

theorem etaHat_inner (x y : Fin 3 → Fin 2) (hx : isMixed3 x) (hy : isMixed3 y) :
    (∑ i : Fin 4, etaHat x i * etaHat y i) =
      if x = y then (1 : ℝ) / 3
      else if hamming3 x = hamming3 y then -(1 : ℝ) / 6 else 0 := by
  have hx_cases := mixed3_cases x hx
  have hy_cases := mixed3_cases y hy
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3ne : Real.sqrt 3 ≠ 0 := by positivity
  rcases hx_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [etaHat, mixedTrineIdx, hamming3, trineVec, Fin.sum_univ_four] <;>
    (try rw [if_neg (by
      intro h
      have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
      simp at h0 h1 h2)]) <;>
    (try field_simp [h3ne]) <;>
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
  have hstar : lambdaStar = (6 * ((2 : ℝ) ^ 31 + 1)) / (6 : ℝ) ^ 32 := by
    unfold lambdaStar; ring
  have h2 : lambda2 = (2 * ((2 : ℝ) ^ 32 + 1)) / (6 : ℝ) ^ 32 := by
    unfold lambda2; ring
  have hrat : lambda2 / lambdaStar = ((2 : ℝ) ^ 32 + 1) / (3 * ((2 : ℝ) ^ 31 + 1)) := by
    rw [h2, hstar]
    have h6 : (6 : ℝ) ^ 32 ≠ 0 := by positivity
    field_simp [h6, hden]
    ring
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
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) hk1
    simpa using hpow
  have habs_half : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
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
    · simp only [Int.cast_zero, add_zero, mul_one, zero_mul]
      linarith
    · by_cases hr0 : 32 - k = 0
      · have hk32_eq : k = 32 := by omega
        subst hk32_eq; norm_num
      · have hr1 : 1 ≤ 32 - k := Nat.pos_of_ne_zero hr0
        have hhalf : (-1 / 2 : ℝ) ^ (32 - k) ≤ 1 / 2 := by
          have habs : |(-1 / 2 : ℝ) ^ (32 - k)| ≤ 1 / 2 := by
            rw [abs_pow, habs_half]
            have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 / 2 : ℝ) ≤ 1) hr1
            simpa using hpow
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
          have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
            (by norm_num : (1 / 4 : ℝ) ≤ 1) hk2
          norm_num at hpow
          exact hpow
        have hpow_le : (-1 / 2 : ℝ) ^ (32 - k) ≤ 1 := by
          have habs : |(-1 / 2 : ℝ) ^ (32 - k)| ≤ 1 := by
            rw [abs_pow, habs_half]
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
      have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) ≤ 1) hk1
      simpa using hpow
    have h4nonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
    nlinarith

end Imscribing.TrilatticeYM
