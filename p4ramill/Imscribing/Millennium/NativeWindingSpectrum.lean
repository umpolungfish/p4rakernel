import Imscribing.Millennium.TrineOperatorAlgebra

namespace Imscribing.Millennium.NativeWindingSpectrum

/-! ## Part 1: Native L5 Register (N, T, F, B), Winding, and Work Filtration -/

def bitN (s : Fin 16) : ℕ := (s.val / 8) % 2
def bitT (s : Fin 16) : ℕ := (s.val / 4) % 2
def bitF (s : Fin 16) : ℕ := (s.val / 2) % 2
def bitB (s : Fin 16) : ℕ := s.val % 2

def unifiedB : Fin 16 := 15

/-- Missing-membership Work count: Work(s) = (1-n) + (1-t) + (1-f) + (1-b). -/
def work (s : Fin 16) : ℕ :=
  (1 - bitN s) + (1 - bitT s) + (1 - bitF s) + (1 - bitB s)

/-- Native L5 ordered inclosure (wind): adds the first missing member in N ≺ T ≺ F ≺ B. -/
def wind (s : Fin 16) : Fin 16 :=
  if bitN s = 0 then ⟨(s.val + 8) % 16, Nat.mod_lt _ (by decide)⟩
  else if bitT s = 0 then ⟨(s.val + 4) % 16, Nat.mod_lt _ (by decide)⟩
  else if bitF s = 0 then ⟨(s.val + 2) % 16, Nat.mod_lt _ (by decide)⟩
  else if bitB s = 0 then ⟨(s.val + 1) % 16, Nat.mod_lt _ (by decide)⟩
  else s

/-- Immediate Glut-adjunction (heldClosure): s ↦ s ∪ {B}. -/
def heldClosure (s : Fin 16) : Fin 16 :=
  if bitB s = 0 then ⟨(s.val + 1) % 16, Nat.mod_lt _ (by decide)⟩ else s

/-- Lifted FDE negation ν(n, t, f, b) = (n, f, t, b). -/
def liftNeg (s : Fin 16) : Fin 16 :=
  ⟨(bitN s * 8 + bitF s * 4 + bitT s * 2 + bitB s) % 16, Nat.mod_lt _ (by decide)⟩

theorem wind_four_steps : ∀ s : Fin 16, wind^[4] s = unifiedB := by
  decide

theorem wind_fixed_iff : ∀ s : Fin 16, wind s = s ↔ s = unifiedB := by
  decide

theorem work_decreases_under_wind :
    ∀ s : Fin 16, s ≠ unifiedB → work (wind s) + 1 = work s := by
  decide

/-- Binomial Work grading dimensions C(4, r) = (1, 4, 6, 4, 1). -/
theorem work_grade_dimensions :
    (Finset.univ.filter fun s : Fin 16 => work s = 0).card = 1 ∧
    (Finset.univ.filter fun s : Fin 16 => work s = 1).card = 4 ∧
    (Finset.univ.filter fun s : Fin 16 => work s = 2).card = 6 ∧
    (Finset.univ.filter fun s : Fin 16 => work s = 3).card = 4 ∧
    (Finset.univ.filter fun s : Fin 16 => work s = 4).card = 1 := by
  decide

/-- Exact rank filtration under iteration: |im(wind^[k])| = 2^(4 - k) = (16, 8, 4, 2, 1). -/
theorem wind_image_rank_filtration :
    (Finset.univ.image (wind^[0])).card = 16 ∧
    (Finset.univ.image (wind^[1])).card = 8 ∧
    (Finset.univ.image (wind^[2])).card = 4 ∧
    (Finset.univ.image (wind^[3])).card = 2 ∧
    (Finset.univ.image (wind^[4])).card = 1 := by
  decide

/-! ## Part 2: Linearized Winding Operator W, Projection E = W⁴, and Nilpotent Index 4 -/

def monomial16 (t : Fin 16 → Fin 16) (c : Fin 16 → ℤ) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if i = t j then c j else 0

theorem monomial16_mul (t₁ t₂ : Fin 16 → Fin 16) (c₁ c₂ : Fin 16 → ℤ) :
    monomial16 t₁ c₁ * monomial16 t₂ c₂ =
    monomial16 (t₁ ∘ t₂) (fun j => c₁ (t₂ j) * c₂ j) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, monomial16, Function.comp_apply]
  rw [Finset.sum_eq_single (t₂ j)]
  · by_cases hi : i = t₁ (t₂ j) <;> simp [hi]
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ (t₂ j)) h

def W_mat : Matrix (Fin 16) (Fin 16) ℤ := monomial16 wind (fun _ => 1)
def E_term : Matrix (Fin 16) (Fin 16) ℤ := monomial16 (fun _ => unifiedB) (fun _ => 1)

theorem W_pow4_eq_E : W_mat^4 = E_term := by
  have h4 : W_mat^4 = monomial16 (wind^[4]) (fun _ => 1) := by
    simp only [pow_succ, pow_zero, one_mul, W_mat, monomial16_mul]
    rfl
  rw [h4]
  apply Matrix.ext
  intro i j
  simp [monomial16, E_term, wind_four_steps]

theorem W_absorbs_E :
    W_mat * E_term = E_term ∧ E_term * W_mat = E_term ∧ E_term * E_term = E_term := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [W_mat, E_term, monomial16_mul]
    apply Matrix.ext; intro i j
    simp [monomial16, show wind unifiedB = unifiedB by decide]

theorem W_pow5_eq_W4 : W_mat^5 = W_mat^4 := by
  rw [pow_succ, W_pow4_eq_E, W_absorbs_E.2.1]

/-- Transient nilpotent operator N_nil = W - E satisfies N_nil⁴ = 0 and N_nil³ ≠ 0. -/
def N_nil : Matrix (Fin 16) (Fin 16) ℤ := W_mat - E_term

private lemma W_pow_mul_E (k : ℕ) : W_mat^k * E_term = E_term := by
  induction k with
  | zero => simp
  | succ r ihr => rw [pow_succ, mul_assoc, W_absorbs_E.1, ihr]

private lemma N_nil_pow_succ (k : ℕ) (hk : 1 ≤ k) : N_nil^k = W_mat^k - E_term := by
  induction k with
  | zero => contradiction
  | succ m ih =>
      cases m with
      | zero => simp only [Nat.zero_add, pow_one, N_nil]
      | succ m' =>
          rw [pow_succ, ih (by omega), N_nil]
          have hWE : W_mat^(m' + 1) * E_term = E_term := W_pow_mul_E (m' + 1)
          have hEW : E_term * W_mat = E_term := W_absorbs_E.2.1
          have hEE : E_term * E_term = E_term := W_absorbs_E.2.2
          rw [sub_mul, mul_sub, mul_sub, ← pow_succ, hWE, hEW, hEE]
          abel

theorem W_transient_nilpotent_index_4 : N_nil^4 = 0 ∧ N_nil^3 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [N_nil_pow_succ 4 (by decide), W_pow4_eq_E, sub_self]
  · intro h
    rw [N_nil_pow_succ 3 (by decide)] at h
    have hW3 : W_mat^3 = monomial16 (wind^[3]) (fun _ => 1) := by
      simp only [pow_succ, pow_zero, one_mul, W_mat, monomial16_mul]
      rfl
    have h140 := congrFun (congrFun h 14) 0
    rw [hW3] at h140
    revert h140
    decide

/-! ## Part 3: Singleton 4 + 12 Block Decomposition and Zero Return Memory (B D^ℓ C = 0) -/

def singList : Fin 4 → Fin 16
  | ⟨0, _⟩ => 8
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 1

def compList : Fin 12 → Fin 16
  | ⟨0, _⟩  => 0
  | ⟨1, _⟩  => 3
  | ⟨2, _⟩  => 5
  | ⟨3, _⟩  => 6
  | ⟨4, _⟩  => 7
  | ⟨5, _⟩  => 9
  | ⟨6, _⟩  => 10
  | ⟨7, _⟩  => 11
  | ⟨8, _⟩  => 12
  | ⟨9, _⟩  => 13
  | ⟨10, _⟩ => 14
  | ⟨11, _⟩ => 15

def projOf {m : ℕ} (p : Fin m → Fin 16) : Matrix (Fin m) (Fin 16) ℤ :=
  fun i s => if p i = s then 1 else 0

def iotaOf {n : ℕ} (q : Fin n → Fin 16) : Matrix (Fin 16) (Fin n) ℤ :=
  fun s j => if q j = s then 1 else 0

def projSing : Matrix (Fin 4) (Fin 16) ℤ := projOf singList
def iotaSing : Matrix (Fin 16) (Fin 4) ℤ := iotaOf singList
def projComp : Matrix (Fin 12) (Fin 16) ℤ := projOf compList
def iotaComp : Matrix (Fin 16) (Fin 12) ℤ := iotaOf compList

theorem singleton_4_plus_12_split :
    projSing * iotaSing = 1 ∧
    projComp * iotaComp = 1 ∧
    iotaSing * projSing + iotaComp * projComp = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

def A_blk : Matrix (Fin 4) (Fin 4) ℤ := projSing * W_mat * iotaSing
def B_blk : Matrix (Fin 4) (Fin 12) ℤ := projSing * W_mat * iotaComp
def C_blk : Matrix (Fin 12) (Fin 4) ℤ := projComp * W_mat * iotaSing
def D_blk : Matrix (Fin 12) (Fin 12) ℤ := projComp * W_mat * iotaComp

private lemma block_entry {m n : ℕ} (p : Fin m → Fin 16) (q : Fin n → Fin 16) (i : Fin m) (j : Fin n) :
    (projOf p * W_mat * iotaOf q) i j =
    if p i = wind (q j) then 1 else 0 := by
  simp only [Matrix.mul_apply, projOf, iotaOf]
  rw [Finset.sum_eq_single (q j)]
  · simp only [ite_true, mul_one]
    rw [Finset.sum_eq_single (wind (q j))]
    · simp [W_mat, monomial16]
    · intro t _ ht
      simp [W_mat, monomial16, ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro s _ hs
    simp [hs.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma A_blk_eq_zero : A_blk = 0 := by
  apply Matrix.ext; intro i j
  dsimp only [A_blk, projSing, iotaSing]
  rw [block_entry]
  simp only [Matrix.zero_apply]
  have : singList i ≠ wind (singList j) := by revert i j; decide
  simp [this]

private lemma B_zero_off_empty : ∀ i : Fin 4, ∀ j : Fin 12, j ≠ 0 → B_blk i j = 0 := by
  intro i j hj
  dsimp only [B_blk, projSing, iotaComp]
  rw [block_entry]
  have : singList i ≠ wind (compList j) := by revert i j hj; decide
  simp [this]

private lemma C_empty_row_zero : ∀ j : Fin 4, C_blk 0 j = 0 := by
  intro j
  dsimp only [C_blk, projComp, iotaSing]
  rw [block_entry]
  have : compList 0 ≠ wind (singList j) := by revert j; decide
  simp [this]

private lemma D_empty_row_zero : ∀ j : Fin 12, D_blk 0 j = 0 := by
  intro j
  dsimp only [D_blk, projComp, iotaComp]
  rw [block_entry]
  have : compList 0 ≠ wind (compList j) := by revert j; decide
  simp [this]

private lemma DC_empty_row_zero (ℓ : ℕ) (j : Fin 4) : (D_blk^ℓ * C_blk) 0 j = 0 := by
  induction ℓ with
  | zero => simpa using C_empty_row_zero j
  | succ m _ =>
      rw [pow_succ', Matrix.mul_assoc, Matrix.mul_apply]
      simp [D_empty_row_zero]

/-- Exact vanishing of all return-memory kernels K_ℓ = B D^ℓ C = 0 (and A = 0) for L5 winding. -/
theorem zero_return_memory :
    A_blk = 0 ∧ ∀ ℓ : ℕ, B_blk * D_blk^ℓ * C_blk = 0 := by
  refine ⟨A_blk_eq_zero, fun ℓ => ?_⟩
  rw [Matrix.mul_assoc]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = 0
  · subst hk; simp [DC_empty_row_zero]
  · simp [B_zero_off_empty i k hk]

/-! ## Part 4: Negation Defect (Rank 2), Glut Commutator (Rank 1), and Bridge Obstruction -/

def N_mat : Matrix (Fin 16) (Fin 16) ℤ := monomial16 liftNeg (fun _ => 1)
def PB_mat : Matrix (Fin 16) (Fin 16) ℤ := monomial16 id (fun s => if bitB s = 1 then 1 else 0)
def PnegB_mat : Matrix (Fin 16) (Fin 16) ℤ := 1 - PB_mat
def HB_mat : Matrix (Fin 16) (Fin 16) ℤ := monomial16 heldClosure (fun _ => 1)

/-- Ordered inclosure commutes with lifted negation on 14 states, failing solely on {N} and {N, B}. -/
theorem wind_negation_comm_iff :
    ∀ s : Fin 16, wind (liftNeg s) = liftNeg (wind s) ↔ ¬ (bitN s = 1 ∧ bitT s = 0 ∧ bitF s = 0) := by
  decide

theorem negation_defect_support :
    ∀ s : Fin 16, s ≠ 8 → s ≠ 9 →
      (W_mat * N_mat - N_mat * W_mat) 0 s = 0 ∧
      (∀ i : Fin 16, (W_mat * N_mat - N_mat * W_mat) i s = 0) := by
  intro s hs8 hs9
  refine ⟨?_, ?_⟩
  · revert s hs8 hs9; decide
  · intro i; revert i s hs8 hs9; decide

theorem negation_defect_values :
    (W_mat * N_mat - N_mat * W_mat) 12 8 = 1 ∧
    (W_mat * N_mat - N_mat * W_mat) 10 8 = -1 ∧
    (W_mat * N_mat - N_mat * W_mat) 13 9 = 1 ∧
    (W_mat * N_mat - N_mat * W_mat) 11 9 = -1 := by
  decide

/-- Glut projection commutes with lifted negation, has no B → ¬B transitions,
    and has rank-1 commutator [P_B, W] = e_{unifiedB} ⊗ e_{NTF}*. -/
theorem glut_sector_laws :
    N_mat * PB_mat = PB_mat * N_mat ∧
    PnegB_mat * W_mat * PB_mat = 0 ∧
    (PB_mat * W_mat - W_mat * PB_mat = fun i j => if i = 15 ∧ j = 14 then 1 else 0) ∧
    W_mat * HB_mat = HB_mat * W_mat ∧
    (∀ s : Fin 16, wind s = heldClosure s ↔ bitN s = 1 ∧ bitT s = 1 ∧ bitF s = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Matrix.ext; intro i j; revert i j; decide
  · apply Matrix.ext; intro i j; revert i j; decide
  · apply Matrix.ext; intro i j; revert i j; decide
  · simp only [W_mat, HB_mat, monomial16_mul]
    apply Matrix.ext; intro i j
    simp [monomial16, show ∀ s : Fin 16, wind (heldClosure s) = heldClosure (wind s) by decide]
  · decide

/-- §57.1 Bridge Obstruction: under the canonical singleton embedding β : L_tri → B ↪ L_native,
    no deterministic map Φ on Fin 16 can intertwine wind (since wind sends {N} ↦ {N, T} outside im β). -/
theorem bridge_obstruction_no_intertwiner
    (rho4 : Fin 16 → Fin 4) (h0 : rho4 0 = 0) :
    let beta : Fin 16 → Fin 16 := fun x => singList (rho4 x)
    ∀ Φ : Fin 16 → Fin 16, ¬ (∀ x : Fin 16, beta (Φ x) = wind (beta x)) := by
  intro beta Φ h
  have hAt0 := h 0
  dsimp [beta] at hAt0
  rw [h0] at hAt0
  have hval : singList (rho4 (Φ 0)) = 12 := by
    simpa [singList, show wind 8 = 12 by decide] using hAt0
  have hne : ∀ b : Fin 4, singList b ≠ 12 := by decide
  exact hne (rho4 (Φ 0)) hval

end Imscribing.Millennium.NativeWindingSpectrum