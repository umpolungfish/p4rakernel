import Mathlib
import Imscribing.Millennium.SIC_D2048_A0Stratum
import Imscribing.Millennium.WienerKhinchinFull

namespace SIC.D2048.WKBridge

open SIC.D2048.A0Stratum
open Imscribing.Millennium.WKExpand
open Erdos220

set_option maxRecDepth 8000

noncomputable section

/-! Rung 1a: the complex embedding of F2048 -/

theorem sq_s2048 : ((Real.sqrt (4190205 : ℝ) : ℝ) : ℂ) * ((Real.sqrt (4190205 : ℝ) : ℝ) : ℂ)
    = (4190205 : ℂ) := by
  rw [← Complex.ofReal_mul (Real.sqrt (4190205:ℝ)) (Real.sqrt (4190205:ℝ)),
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 4190205)]
  norm_num

def s2048 : ℂ := ((Real.sqrt (4190205 : ℝ) : ℝ) : ℂ)

theorem sq_s2048' : s2048 * s2048 = (4190205 : ℂ) := sq_s2048

theorem s2048_ne : s2048 ≠ 0 := by
  intro h
  have := sq_s2048'
  rw [h] at this
  norm_num at this

theorem pow2_s2048 : s2048 ^ 2 = (4190205 : ℂ) := by
  rw [pow_two, sq_s2048']

theorem hd2_0 (x y : ℚ) : ([x, y] : F2048).getD 0 0 = x := rfl

theorem hd2_1 (x y : ℚ) : ([x, y] : F2048).getD 1 0 = y := rfl

/-- getD on the padded list agrees with the original for indices < 2. -/
theorem getD_fpad (v : F2048) (i : ℕ) (hi : i < 2) :
    (fpad v).getD i 0 = v.getD i 0 := by
  match v, i with
  | [], 0 => simp [fpad]
  | [], _ + 1 => simp [fpad]
  | [x], 0 => simp [fpad]
  | [x], _ + 1 => simp [fpad]
  | x :: y :: r, 0 => simp [fpad]
  | x :: y :: r, _ + 1 => simp [fpad]

/-- The complex embedding of F2048 = Q(sqrt 4190205), positive real branch. -/
def phi (v : F2048) : ℂ :=
  (((v.getD 0 0 : ℚ) : ℝ) : ℂ) + (((v.getD 1 0 : ℚ) : ℝ) : ℂ) * s2048

theorem phi_fzero : phi fzero = 0 := by
  simp [phi, fzero, fpad]

theorem phi_fone : phi fone = 1 := by
  simp [phi, fone, fpad]

theorem phi_fadd (a b : F2048) : phi (fadd a b) = phi a + phi b := by
  have h0 := getD_fpad a 0 (by norm_num)
  have h1 := getD_fpad a 1 (by norm_num)
  have h2 := getD_fpad b 0 (by norm_num)
  have h3 := getD_fpad b 1 (by norm_num)
  simp only [phi, fadd, h0, h1, h2, h3]
  rw [hd2_0, hd2_1]
  push_cast
  ring

theorem phi_fmul (a b : F2048) : phi (fmul a b) = phi a * phi b := by
  have h0 := getD_fpad a 0 (by norm_num)
  have h1 := getD_fpad a 1 (by norm_num)
  have h2 := getD_fpad b 0 (by norm_num)
  have h3 := getD_fpad b 1 (by norm_num)
  simp only [phi, fmul, h0, h1, h2, h3, m2048]
  rw [hd2_0, hd2_1]
  push_cast
  ring_nf
  rw [pow2_s2048]

theorem phi_fconj_real (c : F2048) (hc : (fpad c).getD 1 0 = 0) :
    phi (fconj c) = phi c := by
  have h1 := getD_fpad c 1 (by norm_num)
  rw [h1] at hc
  simp only [phi, fconj]
  rw [getD_fpad c 0 (by norm_num), getD_fpad c 1 (by norm_num), hc]
  simp

theorem phi_isReal (c : F2048) (hc : (fpad c).getD 1 0 = 0) :
    star (phi c) = phi c := by
  have h := getD_fpad c 1 (by norm_num)
  rw [h] at hc
  simp only [phi]
  rw [hc]
  simp

theorem phi_zero_of_fisZero (c : F2048) (h : fisZero c = true) : phi c = 0 := by
  simp only [fisZero, Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  rw [getD_fpad c 0 (by norm_num)] at h0
  rw [getD_fpad c 1 (by norm_num)] at h1
  have e0 : c.getD 0 0 = (0 : ℚ) := eq_of_beq h0
  have e1 : c.getD 1 0 = (0 : ℚ) := eq_of_beq h1
  have hp : phi c = (((c.getD 0 0 : ℚ) : ℝ) : ℂ) + (((c.getD 1 0 : ℚ) : ℝ) : ℂ) * s2048 := rfl
  rw [hp, e0, e1]
  simp

theorem fisZero_fone : fisZero fone = false := by
  simp [fisZero, fone, fpad]

/-! Rung 1b: the Fourier root at d = 2048 -/

def w2048 : ℂ := fourierRoot 2048

theorem w2048_one : w2048 ^ 2048 = 1 := by
  have exp_pow_nat : ∀ (z : ℂ) (n : ℕ), Complex.exp z ^ n = Complex.exp ((n : ℂ) * z) := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Complex.exp_add]
  simp only [w2048, fourierRoot, exp_pow_nat]
  have hd : ((2048 : ℕ) : ℂ) ≠ 0 := by norm_num
  rw [mul_comm, div_mul_cancel₀ _ hd]
  exact Complex.exp_eq_one_iff.mpr ⟨1, by ring⟩

theorem w2048_mod (n : ℕ) : w2048 ^ (n % 2048) = w2048 ^ n := by
  have h2 : w2048 ^ n = w2048 ^ (2048 * (n / 2048) + n % 2048) := by
    rw [Nat.div_add_mod n 2048]
  rw [h2, pow_add, pow_mul, w2048_one, one_pow, one_mul]

theorem w2048_char (u v : ℕ) :
    w2048 ^ ((u + v) % 2048) = w2048 ^ (u % 2048) * w2048 ^ (v % 2048) := by
  rw [Nat.add_mod, w2048_mod, pow_add]

/-! Rung 1c: the norm gate and the d = 2048 Wiener-Khinchin wrapper -/

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    List.sum (List.map f (List.range n)) = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem phi_foldl_norm (N : ℕ → F2048) :
    ∀ (l : List ℕ) (s : F2048),
      phi (List.foldl (fun acc k => fadd acc (N k)) s l)
        = phi s + List.sum (List.map (fun k => phi (N k)) l) := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons k l ih =>
    intro s
    rw [List.foldl_cons, ih (fadd s (N k)), phi_fadd]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem norm_gate_sum (N : ℕ → F2048) (hg : norm_gate N = true) :
    ∑ k ∈ Finset.range 2048, phi (N k) = 1 := by
  unfold norm_gate at hg
  have hfold : List.foldl (fun acc k => fadd acc (N k)) fzero (List.range 2048) = fone :=
    eq_of_beq hg
  have hphi := phi_foldl_norm N (List.range 2048) fzero
  rw [hfold, phi_fone, phi_fzero] at hphi
  rw [← list_sum_range (fun k => phi (N k)) 2048]
  calc List.sum (List.map (fun k => phi (N k)) (List.range 2048))
      _ = 0 + List.sum (List.map (fun k => phi (N k)) (List.range 2048)) := (zero_add _).symm
      _ = 1 := hphi.symm

/-- The real modulus data read as a reals-valued function on ZMod 2048. -/
def Nr (N : ℕ → F2048) (k : ZMod 2048) : ℝ := (((fpad (N k.val)).getD 0 0 : ℚ) : ℝ)

/-- Wiener-Khinchin at d = 2048 for real modulus data (wrapper over `wk_full`). -/
theorem wk_2048 (N : ℕ → F2048) (b : ℕ) :
    star (nu 2048 (Nr N) ((b : ZMod 2048))) * nu 2048 (Nr N) ((b : ZMod 2048))
      = ∑ m : ZMod 2048,
          ((corr 2048 (Nr N) m : ℝ) : ℂ) * fourierRoot 2048 ^ (((b : ZMod 2048)) * m).val := by
  exact wk_full 2048 (Nr N) ((b : ZMod 2048))

/-! ## Phase 2: evaluation of sparse ring elements in ℂ -/

/-- Evaluation map: sparse element ↦ ∑ phi c · w^e. -/
def comp (A : RElt) : ℂ := A.foldl (fun acc p => acc + phi p.2 * w2048 ^ (p.1 % 2048)) 0

theorem list_sum_map_mul {α : Type*} {M : Type*} [CommSemiring M] (x : M) (h : α → M)
    (l : List α) :
    List.sum (List.map (fun a => x * h a) l) = x * List.sum (List.map h l) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem foldl_comp_gen (A : RElt) : ∀ c : ℂ,
    (A.foldl (fun acc p => acc + phi p.2 * w2048 ^ (p.1 % 2048)) c)
      = c + List.sum (A.map (fun p : ℕ × F2048 => phi p.2 * w2048 ^ (p.1 % 2048))) := by
  induction A with
  | nil => intro c; simp
  | cons p A ih =>
    intro c
    rw [List.foldl_cons, ih (c + phi p.2 * w2048 ^ (p.1 % 2048))]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem comp_eq_sum (A : RElt) :
    comp A = List.sum (A.map (fun p : ℕ × F2048 => phi p.2 * w2048 ^ (p.1 % 2048))) := by
  unfold comp
  rw [foldl_comp_gen A 0, zero_add]

theorem comp_nil : comp ([] : RElt) = 0 := by
  rw [comp_eq_sum]
  simp

theorem comp_singleton (e : ℕ) (c : F2048) :
    comp ([(e, c)] : RElt) = phi c * w2048 ^ (e % 2048) := by
  rw [comp_eq_sum]
  simp

theorem comp_cons (p : ℕ × F2048) (r : RElt) :
    comp (p :: r) = phi p.2 * w2048 ^ (p.1 % 2048) + comp r := by
  rw [comp_eq_sum (p :: r), List.map_cons, List.sum_cons, comp_eq_sum r]

theorem mod_mod_2048 (n : ℕ) : n % 2048 % 2048 = n % 2048 :=
  Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))

theorem comp_rinsert (c : F2048) : ∀ (acc : RElt) (e : ℕ),
    comp (rinsert acc e c) = comp acc + phi c * w2048 ^ (e % 2048) := by
  by_cases hz : fisZero c = true
  case pos =>
    intro acc e
    unfold rinsert
    rw [if_pos hz, phi_zero_of_fisZero c hz, zero_mul, add_zero]
  case neg =>
    intro acc
    induction acc with
    | nil =>
      intro e
      rw [rinsert, if_neg hz]
      simp only []
      rw [comp_singleton, comp_nil]
      simp
    | cons p r ih =>
      intro e
      by_cases hlt : e % 2048 < p.1
      · rw [rinsert, if_neg hz]
        simp only []
        rw [if_pos hlt]
        simp only [comp_cons, mod_mod_2048]
        ring
      · by_cases heq : e % 2048 = p.1
        · have hdec : (e % 2048 == p.1) = true := by rw [heq]; simp
          rw [rinsert, if_neg hz]
          simp only []
          rw [if_neg hlt, if_pos hdec]
          by_cases hw : fisZero (fadd p.2 c) = true
          · rw [if_pos hw, comp_cons, heq, ← w2048_mod p.1]
            have hpc : phi p.2 + phi c = 0 := by
              rw [← phi_fadd]
              exact phi_zero_of_fisZero (fadd p.2 c) hw
            have hzero : phi p.2 * w2048 ^ (p.1 % 2048) + phi c * w2048 ^ (p.1 % 2048) = 0 := by
              rw [mul_comm (phi p.2) (w2048 ^ (p.1 % 2048)),
                mul_comm (phi c) (w2048 ^ (p.1 % 2048)), ← mul_add, hpc, mul_zero]
            -- goal: comp r = (a + comp r) + b with a + b = 0
            rw [add_assoc, add_comm (comp r) (phi c * w2048 ^ (p.1 % 2048)), ← add_assoc,
              hzero, zero_add]
          · rw [if_neg hw, comp_cons, comp_cons, heq, phi_fadd, ← w2048_mod p.1]
            simp only []
            ring
        · have hdec : ¬((e % 2048 == p.1) = true) := by rw [beq_iff_eq]; exact heq
          rw [rinsert, if_neg hz]
          simp only []
          rw [if_neg hlt, if_neg hdec, comp_cons, comp_cons, ih (e % 2048), mod_mod_2048]
          ring

theorem comp_radd_gen (B : RElt) : ∀ A : RElt,
    comp (B.foldl (fun acc p => rinsert acc p.1 p.2) A) = comp A + comp B := by
  induction B with
  | nil => intro A; rw [List.foldl_nil, comp_nil, add_zero]
  | cons p B ih =>
    intro A
    simp only [List.foldl_cons]
    rw [ih (rinsert A p.1 p.2), comp_rinsert, comp_cons]
    ring

theorem comp_radd (A B : RElt) : comp (radd A B) = comp A + comp B := by
  rw [show radd A B = B.foldl (fun acc p => rinsert acc p.1 p.2) A from rfl]
  exact comp_radd_gen B A

theorem comp_foldl_rmul_inner (B : RElt) (p : ℕ × F2048) : ∀ acc : RElt,
    comp (B.foldl (fun acc2 q => radd acc2 (rmulTerm p.1 p.2 q.1 q.2)) acc)
      = comp acc + List.sum (B.map (fun q : ℕ × F2048 => comp (rmulTerm p.1 p.2 q.1 q.2))) := by
  induction B with
  | nil => intro acc; simp
  | cons q B ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (radd acc (rmulTerm p.1 p.2 q.1 q.2)), comp_radd]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem comp_rmulTerm (e1 : ℕ) (c1 : F2048) (e2 : ℕ) (c2 : F2048) :
    comp (rmulTerm e1 c1 e2 c2) = phi c1 * phi c2 * w2048 ^ ((e1 + e2) % 2048) := by
  unfold rmulTerm
  rw [comp_rinsert]
  simp [comp_nil, phi_fmul]

theorem comp_rmul_sum (p : ℕ × F2048) (B : RElt) :
    List.sum (B.map (fun q : ℕ × F2048 => comp (rmulTerm p.1 p.2 q.1 q.2)))
      = phi p.2 * w2048 ^ (p.1 % 2048) * comp B := by
  induction B with
  | nil => rw [List.map_nil, List.sum_nil, comp_nil, mul_zero]
  | cons q B ih =>
    simp only [List.map_cons, List.sum_cons, ih, comp_cons]
    rw [comp_rmulTerm, w2048_char]
    ring

theorem comp_rmul_gen (B : RElt) : ∀ A : RElt, ∀ acc : RElt,
    comp (A.foldl (fun acc p => B.foldl (fun acc2 q => radd acc2 (rmulTerm p.1 p.2 q.1 q.2)) acc) acc)
      = comp acc + comp A * comp B := by
  intro A
  induction A with
  | nil => intro acc; rw [List.foldl_nil, comp_nil, zero_mul, add_zero]
  | cons p A ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (B.foldl (fun acc2 q => radd acc2 (rmulTerm p.1 p.2 q.1 q.2)) acc),
      comp_foldl_rmul_inner B p acc, comp_rmul_sum, comp_cons]
    ring

theorem comp_rmul_hom (A B : RElt) : comp (rmul A B) = comp A * comp B := by
  have hrfl : rmul A B
      = A.foldl (fun acc p => B.foldl (fun acc2 q => radd acc2 (rmulTerm p.1 p.2 q.1 q.2)) acc) [] :=
    rfl
  rw [hrfl, comp_rmul_gen B A [], comp_nil, zero_add]

theorem comp_rK (c : F2048) : comp (rK c) = phi c := by
  unfold rK
  rw [comp_rinsert, comp_nil]
  simp [Nat.zero_mod, pow_zero]

theorem comp_omegaPow (e : ℕ) : comp (omegaPow e) = w2048 ^ (e % 2048) := by
  unfold omegaPow
  rw [comp_rinsert, comp_nil]
  simp [phi_fone]

theorem comp_overlap_term (c : F2048) (e : ℕ) :
    comp (rmul (rK c) (omegaPow e)) = phi c * w2048 ^ (e % 2048) := by
  rw [comp_rmul_hom, comp_rK, comp_omegaPow]

/-! ## Phase 3: bridging comp to the ν-spectrum -/

theorem comp_foldl_overlap (N : ℕ → F2048) (b : ℕ) : ∀ (l : List ℕ) (acc : RElt),
    comp (l.foldl (fun acc k => radd acc (rmul (rK (N k)) (omegaPow (b * k)))) acc)
      = comp acc + List.sum (l.map (fun k : ℕ => comp (rmul (rK (N k)) (omegaPow (b * k))))) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons k l ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (radd acc (rmul (rK (N k)) (omegaPow (b * k)))), comp_radd]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem list_map_congr {α β : Type*} {f g : α → β} (h : ∀ a : α, f a = g a) (l : List α) :
    List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.map_cons, h, ih]

theorem list_map_congr_mem {α β : Type*} {f g : α → β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.map_cons, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
      h a (by simp)]

theorem comp_overlap_a0 (N : ℕ → F2048) (b : ℕ) :
    comp (overlap_a0 N b)
      = List.sum ((List.range 2048).map (fun k : ℕ => phi (N k) * w2048 ^ ((b * k) % 2048))) := by
  unfold overlap_a0
  simp only [rzero]
  rw [comp_foldl_overlap N b (List.range 2048) ([] : RElt), comp_nil, zero_add]
  rw [list_map_congr (fun k : ℕ => comp_overlap_term (N k) (b * k))]

/-- The canonical index bijection Fin 2048 ≃ ZMod 2048. -/
def finEquivZMod : Fin 2048 ≃ ZMod 2048 :=
  { toFun := fun i => ((i : ℕ) : ZMod 2048)
    invFun := fun k => ⟨k.val, ZMod.val_lt k⟩
    left_inv := by
      intro i
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Fin.ext_iff]
    right_inv := by
      intro k
      simp [ZMod.natCast_val] }

theorem zmod_sum_range {M : Type*} [AddCommMonoid M] (g : ZMod 2048 → M) :
    ∑ k : ZMod 2048, g k = ∑ k ∈ Finset.range 2048, g ((k : ZMod 2048)) := by
  rw [Fintype.sum_equiv finEquivZMod.symm (fun k : ZMod 2048 => g k)
    (fun i : Fin 2048 => g (finEquivZMod i))
    (fun x => (congrArg g (finEquivZMod.apply_symm_apply x)).symm)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => g ((i : ℕ) : ZMod 2048)) 2048).symm

theorem phi_Nr (N : ℕ → F2048) (hN : ∀ k : ℕ, (fpad (N k)).getD 1 0 = 0)
    (k : ℕ) (hk : k < 2048) :
    phi (N k) = ((Nr N ((k : ℕ) : ZMod 2048) : ℝ) : ℂ) := by
  unfold phi Nr
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [← getD_fpad (N k) 0 (by norm_num), ← getD_fpad (N k) 1 (by norm_num), hN k]
  simp

theorem comp_overlap_eq_nu (N : ℕ → F2048) (b : ℕ) (hN : ∀ k : ℕ, (fpad (N k)).getD 1 0 = 0) :
    comp (overlap_a0 N b) = nu 2048 (Nr N) ((b : ZMod 2048)) := by
  rw [comp_overlap_a0]
  unfold nu
  rw [zmod_sum_range]
  rw [list_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < 2048 := Finset.mem_range.mp hk
  have hphi := phi_Nr N hN k hklt
  have hexp : ((b : ZMod 2048) * (k : ZMod 2048)).val = (b * k) % 2048 := by
    rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast, ← Nat.mul_mod]
  rw [hphi, hexp]
  rfl

theorem a0_spectrum (N : ℕ → F2048) (b : ℕ) (hN : ∀ k : ℕ, (fpad (N k)).getD 1 0 = 0) :
    star (comp (overlap_a0 N b)) * comp (overlap_a0 N b)
      = ∑ m : ZMod 2048, ((corr 2048 (Nr N) m : ℝ) : ℂ) * fourierRoot 2048 ^ (((b : ZMod 2048)) * m).val := by
  rw [comp_overlap_eq_nu N b hN]
  exact wk_2048 N b

theorem nu0_of_norm_gate (N : ℕ → F2048) (hN : ∀ k : ℕ, (fpad (N k)).getD 1 0 = 0)
    (hg : norm_gate N = true) :
    nu 2048 (Nr N) ((0 : ℕ) : ZMod 2048) = 1 := by
  rw [← comp_overlap_eq_nu N 0 hN, comp_overlap_a0]
  rw [list_map_congr (g := fun a : ℕ => phi (N a)) (fun a : ℕ => by simp) (List.range 2048)]
  rw [list_sum_range]
  exact norm_gate_sum N hg

end
end SIC.D2048.WKBridge
