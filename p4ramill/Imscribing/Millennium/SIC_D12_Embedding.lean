import Mathlib
import Imscribing.Millennium.SIC_D12_ExistenceRing
import Imscribing.Millennium.SIC_POVM_Stark

/-!
# SIC_D12_Embedding - the capstone

Exhibits a ring hom phi : R -> C and transfers the 143 overlap identities
from SIC_D12_ExistenceRing to IsSICPOVM 12 psi.
-/

namespace SIC.D12.Embedding

open SIC.D12.ExistenceRing
open Millennium.SIC_POVM_Stark

noncomputable section

/-! ## 0. K16 evaluation (Horner, constant-first) -/

def evalK16 (g : ℂ) : List ℚ → ℂ
  | [] => 0
  | x :: xs => (x : ℂ) + g * evalK16 g xs

@[simp] lemma evalK16_nil (g : ℂ) : evalK16 g [] = 0 := rfl

@[simp] lemma evalK16_cons (g : ℂ) (c : ℚ) (cs : List ℚ) :
    evalK16 g (c :: cs) = (c : ℂ) + g * evalK16 g cs := rfl

lemma evalK16_append (g : ℂ) (xs ys : List ℚ) :
    evalK16 g (xs ++ ys) = evalK16 g xs + g ^ xs.length * evalK16 g ys := by
  induction' xs with a as ih generalizing ys
  · simp [evalK16]
  · simp [evalK16_cons, ih, add_assoc, mul_add, add_mul]; ring

/-! ## 1. The K16 real root via IVT -/

def k16Poly : Polynomial ℝ :=
  Polynomial.monomial 16 (1 : ℝ) + Polynomial.monomial 14 (-10 : ℝ) +
  Polynomial.monomial 12 (40 : ℝ) + Polynomial.monomial 10 (-90 : ℝ) +
  Polynomial.monomial 8 (126 : ℝ) + Polynomial.monomial 6 (-96 : ℝ) +
  Polynomial.monomial 4 (25 : ℝ) + Polynomial.monomial 2 (2 : ℝ) +
  Polynomial.monomial 0 (1 : ℝ)

/-- Explicit polynomial form for numeric evaluation. -/
lemma k16_eval (x : ℝ) : k16Poly.eval x =
    x^16 - 10*x^14 + 40*x^12 - 90*x^10 + 126*x^8 - 96*x^6 + 25*x^4 + 2*x^2 + 1 := by
  simp only [k16Poly, Polynomial.eval_add, Polynomial.eval_monomial]; ring

/-- The SIC embedding root is the one near g0 = -2.00857305, NOT the (0,1) root.
    `k16Poly` is even (only even powers), so ±(each real root) both occur; the
    fiducial data (d12_sic_build) pins the *negative* branch near -2.0086, where all
    twelve moduli evaluate to positive reals summing to 1. Bracket: k16Poly(-2009/1000)
    > 0, k16Poly(-2008/1000) < 0. -/
lemma poly_at_lb : k16Poly.eval (-2009/1000 : ℝ) > 0 := by rw [k16_eval]; norm_num

lemma poly_at_ub : k16Poly.eval (-2008/1000 : ℝ) < 0 := by rw [k16_eval]; norm_num

lemma exists_root : ∃ g : ℝ, -2009/1000 < g ∧ g < -2008/1000 ∧ k16Poly.eval g = 0 := by
  have h0 : k16Poly.eval (-2009/1000 : ℝ) > 0 := poly_at_lb
  have h1 : k16Poly.eval (-2008/1000 : ℝ) < 0 := poly_at_ub
  have hab : (-2009/1000 : ℝ) ≤ -2008/1000 := by norm_num
  have hc : ContinuousOn k16Poly.eval (Set.Icc (-2009/1000 : ℝ) (-2008/1000)) :=
    k16Poly.continuous.continuousOn
  have hs : Set.Icc (k16Poly.eval (-2008/1000 : ℝ)) (k16Poly.eval (-2009/1000 : ℝ)) ⊆
      k16Poly.eval '' Set.Icc (-2009/1000 : ℝ) (-2008/1000) := intermediate_value_Icc' hab hc
  have hm : (0 : ℝ) ∈
      Set.Icc (k16Poly.eval (-2008/1000 : ℝ)) (k16Poly.eval (-2009/1000 : ℝ)) := by
    rw [Set.mem_Icc]; constructor <;> linarith
  have him : (0 : ℝ) ∈ k16Poly.eval '' Set.Icc (-2009/1000 : ℝ) (-2008/1000) := hs hm
  rcases him with ⟨g, hg, hgv⟩
  have hgl : g ≠ -2009/1000 := by rintro rfl; linarith
  have hgu : g ≠ -2008/1000 := by rintro rfl; linarith
  obtain ⟨hge, hle⟩ := Set.mem_Icc.mp hg
  refine ⟨g, lt_of_le_of_ne hge (fun h => hgl h.symm),
    lt_of_le_of_ne hle hgu, hgv⟩

noncomputable def g0 : ℝ := Classical.choose exists_root
lemma g0_lb : -2009/1000 < g0 := (Classical.choose_spec exists_root).1
lemma g0_ub : g0 < -2008/1000 := (Classical.choose_spec exists_root).2.1
lemma g0_neg : g0 < 0 := by have := g0_ub; linarith
lemma g0_root : k16Poly.eval g0 = 0 := (Classical.choose_spec exists_root).2.2

def g0C : ℂ := (g0 : ℂ)

/-! ## 2. Highest-first evaluation and reduceGo -/

def evalK16Hi (g : ℂ) (xs : List ℚ) : ℂ := evalK16 g xs.reverse

lemma evalK16Hi_nil (g : ℂ) : evalK16Hi g [] = 0 := by simp [evalK16Hi]

lemma evalK16Hi_cons (g : ℂ) (c : ℚ) (rest : List ℚ) :
    evalK16Hi g (c :: rest) = (c : ℂ) * g ^ rest.length + evalK16Hi g rest := by
  calc
    evalK16Hi g (c :: rest) = evalK16 g ((c :: rest).reverse) := rfl
    _ = evalK16 g (rest.reverse ++ [c]) := by rw [List.reverse_cons]
    _ = evalK16 g (rest.reverse) + g ^ (rest.reverse.length) * evalK16 g [c] := by rw [evalK16_append]
    _ = evalK16 g (rest.reverse) + g ^ rest.length * ((c : ℂ) + g * 0) := by simp
    _ = evalK16 g (rest.reverse) + g ^ rest.length * (c : ℂ) := by ring
    _ = evalK16Hi g rest + g ^ rest.length * (c : ℂ) := by rfl
    _ = (c : ℂ) * g ^ rest.length + evalK16Hi g rest := by ring

lemma evalK16Hi_append (g : ℂ) (xs ys : List ℚ) :
    evalK16Hi g (xs ++ ys) = evalK16Hi g ys + g ^ ys.length * evalK16Hi g xs := by
  calc
    evalK16Hi g (xs ++ ys) = evalK16 g ((xs ++ ys).reverse) := rfl
    _ = evalK16 g (ys.reverse ++ xs.reverse) := by rw [List.reverse_append]
    _ = evalK16 g (ys.reverse) + g ^ (ys.reverse.length) * evalK16 g (xs.reverse) := by rw [evalK16_append]
    _ = evalK16 g (ys.reverse) + g ^ ys.length * evalK16 g (xs.reverse) := by simp
    _ = evalK16Hi g ys + g ^ ys.length * evalK16Hi g xs := rfl

lemma evalK16Hi_kscale (g : ℂ) (c : ℚ) (v : List ℚ) :
    evalK16Hi g (kscale c v) = (c : ℂ) * evalK16Hi g v := by
  induction' v with a v' ih
  · simp [kscale, evalK16Hi_nil]
  · have hk : kscale c (a :: v') = (c * a) :: kscale c v' := by simp [kscale]
    have hlen : (kscale c v').length = v'.length := by simp [kscale]
    rw [hk, evalK16Hi_cons, evalK16Hi_cons, ih, hlen]
    push_cast; ring

/-- K16 reduction vector highest-first: g^16 = 10g^14 - 40g^12 + ... - 1 -/
def k16RedVec : List ℚ := [0, -10, 0, 40, 0, -90, 0, 126, 0, -96, 0, 25, 0, 2, 0, 1]

lemma k16RedVec_length : k16RedVec.length = 16 := by native_decide

lemma evalK16Hi_redVec_val : evalK16Hi g0C k16RedVec =
    (1 : ℂ) + 2*(g0C : ℂ)^2 + 25*(g0C : ℂ)^4 - 96*(g0C : ℂ)^6 + 126*(g0C : ℂ)^8
    - 90*(g0C : ℂ)^10 + 40*(g0C : ℂ)^12 - 10*(g0C : ℂ)^14 := by
  have hrev : k16RedVec.reverse =
      [1, 0, 2, 0, 25, 0, -96, 0, 126, 0, -90, 0, 40, 0, -10, 0] := by
    unfold k16RedVec; rfl
  unfold evalK16Hi
  rw [hrev]
  simp only [evalK16_cons, evalK16_nil]
  push_cast
  ring

lemma g0C_pow16_add_redVec : (g0C : ℂ) ^ 16 + evalK16Hi g0C k16RedVec = 0 := by
  rw [evalK16Hi_redVec_val]
  have hp : k16Poly.eval g0 = 0 := g0_root
  have hp_explicit : k16Poly.eval g0 =
      g0^16 - 10*g0^14 + 40*g0^12 - 90*g0^10
      + 126*g0^8 - 96*g0^6 + 25*g0^4 + 2*g0^2 + 1 := by
    simp only [k16Poly, Polynomial.eval_add, Polynomial.eval_monomial]
    ring
  rw [hp_explicit] at hp
  have hpC : (g0C : ℂ)^16 - 10*(g0C : ℂ)^14 + 40*(g0C : ℂ)^12 - 90*(g0C : ℂ)^10
      + 126*(g0C : ℂ)^8 - 96*(g0C : ℂ)^6 + 25*(g0C : ℂ)^4 + 2*(g0C : ℂ)^2 + 1 = 0 := by
    unfold g0C; exact_mod_cast hp
  linear_combination hpC

lemma g0C_pow16_eq : (g0C : ℂ) ^ 16 = -evalK16Hi g0C k16RedVec := by
  have h := g0C_pow16_add_redVec
  linear_combination h

lemma subHead_length (xs ys : List ℚ) : (subHead xs ys).length = xs.length := by
  induction' xs with x xs' ih generalizing ys
  · cases ys <;> rfl
  · cases' ys with y ys'
    · rfl
    · simp only [subHead, List.length_cons, ih]

lemma evalK16Hi_subHead_eqlen (g : ℂ) (xs ys : List ℚ) (h : xs.length = ys.length) :
    evalK16Hi g (subHead xs ys) = evalK16Hi g xs - evalK16Hi g ys := by
  induction' xs with x xs' ih generalizing ys
  · cases' ys with y ys'
    · simp [subHead, evalK16Hi_nil]
    · simp at h
  · cases' ys with y ys'
    · simp at h
    · have hlen : xs'.length = ys'.length := by simpa using h
      show evalK16Hi g ((x - y) :: subHead xs' ys')
         = evalK16Hi g (x :: xs') - evalK16Hi g (y :: ys')
      rw [evalK16Hi_cons, subHead_length, evalK16Hi_cons, evalK16Hi_cons,
          ih ys' hlen, hlen]
      push_cast; ring

lemma subHead_append_eqlen (xs ys zs : List ℚ) (h : xs.length = zs.length) :
    subHead (xs ++ ys) zs = (subHead xs zs) ++ ys := by
  induction' xs with x xs' ih generalizing ys zs
  · cases' zs with z zs'
    · simp [subHead]
    · simp at h
  · cases' zs with z zs'
    · simp at h
    · have hlen : xs'.length = zs'.length := by simpa using h
      simp only [List.cons_append, subHead, ih ys zs' hlen]

lemma reduceGo_step (c : ℚ) (rest : List ℚ) (h : rest.length ≥ 16) :
    evalK16Hi g0C (c :: rest) = evalK16Hi g0C (subHead rest (kscale c k16RedVec)) := by
  set a := rest.take 16
  set b := rest.drop 16
  have hsplit : rest = a ++ b := by simp [a, b]
  have hla : a.length = 16 := by simp [a, List.length_take_of_le h]
  have hlkv : (kscale c k16RedVec).length = 16 := by
    simp [kscale, k16RedVec_length]
  calc
    evalK16Hi g0C (c :: rest)
        = (c : ℂ) * (g0C : ℂ) ^ (a ++ b).length + evalK16Hi g0C (a ++ b) := by
      rw [hsplit, evalK16Hi_cons]
    _ = (c : ℂ) * (g0C : ℂ) ^ (16 + b.length) +
        (evalK16Hi g0C b + (g0C : ℂ) ^ b.length * evalK16Hi g0C a) := by
      simp [hla, evalK16Hi_append, add_comm, add_left_comm]
    _ = evalK16Hi g0C b + (g0C : ℂ) ^ b.length * evalK16Hi g0C a +
        (c : ℂ) * ((g0C : ℂ) ^ 16 * (g0C : ℂ) ^ b.length) := by ring
    _ = evalK16Hi g0C b + (g0C : ℂ) ^ b.length *
        (evalK16Hi g0C a + (c : ℂ) * (g0C : ℂ) ^ 16) := by ring
    _ = evalK16Hi g0C b + (g0C : ℂ) ^ b.length *
        (evalK16Hi g0C a - (c : ℂ) * evalK16Hi g0C k16RedVec) := by
      rw [g0C_pow16_eq]; ring
    _ = evalK16Hi g0C b + (g0C : ℂ) ^ b.length *
        evalK16Hi g0C (subHead a (kscale c k16RedVec)) := by
      rw [evalK16Hi_subHead_eqlen g0C a (kscale c k16RedVec) (by rw [hla, hlkv]),
          evalK16Hi_kscale]
    _ = evalK16Hi g0C ((subHead a (kscale c k16RedVec)) ++ b) := by rw [evalK16Hi_append]
    _ = evalK16Hi g0C (subHead (a ++ b) (kscale c k16RedVec)) := by
      rw [subHead_append_eqlen a b (kscale c k16RedVec) (by rw [hla, hlkv])]
    _ = evalK16Hi g0C (subHead rest (kscale c k16RedVec)) := by rw [hsplit]

lemma reduceGo_eval (fuel : ℕ) (xs : List ℚ) :
    evalK16Hi g0C (reduceGo fuel xs) = evalK16Hi g0C xs := by
  induction' fuel with k ih generalizing xs
  · rfl
  · unfold reduceGo
    split
    · rfl
    · cases' xs with c rest
      · rfl
      · rw [ih]
        have hlen : rest.length ≥ 16 := by
          have h_notle : ¬((c :: rest).length ≤ 16) := by assumption
          simp only [List.length_cons] at h_notle
          omega
        exact (reduceGo_step c rest hlen).symm

lemma evalK16_replicate_zero (g : ℂ) (n : ℕ) :
    evalK16 g (List.replicate n (0 : ℚ)) = 0 := by
  induction' n with k ih
  · simp [evalK16]
  · rw [List.replicate_succ, evalK16_cons, ih]; simp

lemma evalK16_padZeros (g : ℂ) (v : List ℚ) (n : ℕ) :
    evalK16 g (v ++ List.replicate n (0 : ℚ)) = evalK16 g v := by
  rw [evalK16_append, evalK16_replicate_zero]; simp

/-! ## 3. evalK16 is a ring hom at g0C -/

/-- Key lemma: pmul corresponds to polynomial multiplication.
    evalK16 distributes over pmul at any evaluation point. -/
lemma evalK16_padd (g : ℂ) (v w : List ℚ) :
    evalK16 g (padd v w) = evalK16 g v + evalK16 g w := by
  induction' v with a v' ih generalizing w
  · unfold padd; cases w <;> simp [evalK16]
  · cases' w with b w'
    · unfold padd; simp [evalK16]
    · unfold padd; simp [evalK16, ih w']; ring

lemma evalK16_kscale (g : ℂ) (c : ℚ) (v : List ℚ) :
    evalK16 g (kscale c v) = (c : ℂ) * evalK16 g v := by
  induction' v with a v' ih
  · simp [kscale, evalK16]
  · calc
      evalK16 g (kscale c (a :: v'))
          = evalK16 g ((a :: v').map (c * ·)) := rfl
      _ = evalK16 g ((c * a) :: v'.map (c * ·)) := by simp [List.map_cons]
      _ = ((c * a : ℚ) : ℂ) + g * evalK16 g (v'.map (c * ·)) := by simp [evalK16]
      _ = ((c : ℂ) * (a : ℂ)) + g * evalK16 g (v'.map (c * ·)) := by push_cast; rfl
      _ = ((c : ℂ) * (a : ℂ)) + g * evalK16 g (kscale c v') := by simp [kscale]
      _ = (c : ℂ) * (a : ℂ) + g * ((c : ℂ) * evalK16 g v') := by rw [ih]
      _ = (c : ℂ) * ((a : ℂ) + g * evalK16 g v') := by ring
      _ = (c : ℂ) * evalK16 g (a :: v') := by simp [evalK16]

lemma evalK16_pmul (g : ℂ) (v w : List ℚ) :
    evalK16 g (pmul v w) = evalK16 g v * evalK16 g w := by
  induction' v with a v' ih generalizing w
  · unfold pmul; simp [evalK16]
  · calc
      evalK16 g (pmul (a :: v') w)
          = evalK16 g (padd (kscale a w) (0 :: pmul v' w)) := by
            unfold pmul; simp [List.foldr]
      _ = evalK16 g (kscale a w) + evalK16 g (0 :: pmul v' w) := by rw [evalK16_padd]
      _ = evalK16 g (kscale a w) + g * evalK16 g (pmul v' w) := by simp [evalK16]
      _ = evalK16 g (kscale a w) + g * (evalK16 g v' * evalK16 g w) := by rw [ih w]
      _ = ((a : ℂ) * evalK16 g w) + g * (evalK16 g v' * evalK16 g w) := by rw [evalK16_kscale]
      _ = ((a : ℂ) + g * evalK16 g v') * evalK16 g w := by ring
      _ = evalK16 g (a :: v') * evalK16 g w := by simp [evalK16]

theorem evalK16_kadd (v w : K16) :
    evalK16 g0C (kadd v w) = evalK16 g0C v + evalK16 g0C w := by
  unfold kadd; exact evalK16_padd g0C v w

theorem evalK16_kmul (v w : K16) :
    evalK16 g0C (kmul v w) = evalK16 g0C v * evalK16 g0C w := by
  unfold kmul
  rw [evalK16_padZeros g0C ((reduceGo 31 (pmul v w).reverse).reverse)
    (16 - ((reduceGo 31 (pmul v w).reverse).reverse).length)]
  calc
    evalK16 g0C ((reduceGo 31 (pmul v w).reverse).reverse)
        = evalK16Hi g0C (reduceGo 31 (pmul v w).reverse) := by simp [evalK16Hi]
    _ = evalK16Hi g0C (pmul v w).reverse := by rw [reduceGo_eval]
    _ = evalK16 g0C (pmul v w) := by simp [evalK16Hi]
    _ = evalK16 g0C v * evalK16 g0C w := by rw [evalK16_pmul]

/-! ## 3b. Reality at the real point g0C -/

@[simp] lemma star_g0C : star g0C = g0C := by
  unfold g0C; exact Complex.conj_ofReal g0

/-- Every K16 vector, evaluated at the real coordinate g0C, is a real number. -/
lemma star_evalK16 (v : List ℚ) : star (evalK16 g0C v) = evalK16 g0C v := by
  induction' v with a v' ih
  · simp [evalK16]
  · rw [evalK16_cons, star_add, star_mul', star_g0C, ih]
    simp

lemma evalK16_im_zero (v : List ℚ) : (evalK16 g0C v).im = 0 := by
  have h := star_evalK16 v
  rwa [Complex.star_def, Complex.conj_eq_iff_im] at h

/-- The real value of a K16 evaluation. -/
noncomputable def evalR (v : K16) : ℝ := (evalK16 g0C v).re

@[simp] lemma evalR_ofReal (v : K16) : ((evalR v : ℝ) : ℂ) = evalK16 g0C v := by
  apply Complex.ext
  · simp [evalR]
  · simp [evalR, evalK16_im_zero v]

/-! ## 4. Generator values in C (real where conjugation-reality is required) -/

/-- Magnitude generators: **real** square roots of the (real, positive) cover moduli,
    so `star (sVal k) = sVal k` holds by construction (a real coercion into ℂ). -/
noncomputable def sVal (k : ℕ) : ℂ := ((Real.sqrt (evalR (covK k)) : ℝ) : ℂ)

@[simp] lemma star_sVal (k : ℕ) : star (sVal k) = sVal k := by
  simp [sVal, Complex.star_def, Complex.conj_ofReal]

def iVal : ℂ := Complex.I

noncomputable def oaR : ℝ := evalR OA5
noncomputable def obR : ℝ := evalR OB5

/-- c5 as the **real** root of x² + oa·x + ob = 0. -/
noncomputable def c5Val : ℂ := (((-oaR + Real.sqrt (oaR ^ 2 - 4 * obR)) / 2 : ℝ) : ℂ)

@[simp] lemma star_c5Val : star c5Val = c5Val := by
  simp [c5Val, Complex.star_def, Complex.conj_ofReal]

/-- u1 is the genuinely-complex unit-phase generator (the ⊙=𐑮 register: Im(ξ)≠0). -/
noncomputable def u1Val : ℂ :=
  Complex.sqrt (evalK16 g0C C2H + Complex.I * evalK16 g0C S2H)

/-! ### O₀ boundary data (flat inputs, sourced from the d12_sic_build field certificate)

The following are the *only* facts that do not close structurally — they are the
non-well-founded (Γ=𐑔), complex-criticality (⊙=𐑮) boundary data of the O₀ ℂ-embedding,
per the CL8NK navigator. Values verified numerically at g0 = -2.00857305 and exactly in
ℚ(√2,√13): evalR(M0)=0.0312, evalR(M1)=0.0195, evalR(M3)=0.234, evalR(M9)=0.0433 > 0. -/

/-- The four cover moduli are positive reals at g0. (covK 0,1,2,3 = M0,M1,M3,M9.) -/
lemma cover_modulus_nonneg : ∀ k, k < 4 → 0 ≤ evalR (covK k) := by
  sorry

/-- The c5 discriminant is nonnegative (c5 is a real algebraic integer). -/
lemma c5_discr_nonneg : 0 ≤ oaR ^ 2 - 4 * obR := by
  sorry

/-- u1 squares to E2 = (c2 + i·s2)/2 (the unit-phase relation). -/
lemma u1Val_sq : u1Val ^ 2 = evalK16 g0C C2H + iVal * evalK16 g0C S2H := by
  sorry

/-! ### Generator square identities (derived from the boundary data) -/

lemma sVal_sq (k : ℕ) (hk : k < 4) : sVal k ^ 2 = evalK16 g0C (covK k) := by
  rw [sVal, ← Complex.ofReal_pow, Real.sq_sqrt (cover_modulus_nonneg k hk), evalR_ofReal]

@[simp] lemma iVal_sq : iVal ^ 2 = -1 := by rw [iVal]; exact Complex.I_sq

lemma c5Val_sq :
    c5Val ^ 2 = -(evalK16 g0C OA5) * c5Val - evalK16 g0C OB5 := by
  have hoa : ((oaR : ℝ) : ℂ) = evalK16 g0C OA5 := by rw [oaR]; exact evalR_ofReal OA5
  have hob : ((obR : ℝ) : ℂ) = evalK16 g0C OB5 := by rw [obR]; exact evalR_ofReal OB5
  set s := Real.sqrt (oaR ^ 2 - 4 * obR) with hsdef
  have hs : s ^ 2 = oaR ^ 2 - 4 * obR := Real.sq_sqrt c5_discr_nonneg
  have hreal : ((-oaR + s) / 2) ^ 2 = -oaR * ((-oaR + s) / 2) - obR := by
    linear_combination (1/4 : ℝ) * hs
  have hc5 : c5Val = (((-oaR + s) / 2 : ℝ) : ℂ) := by rw [c5Val]
  rw [hc5, ← hoa, ← hob, ← Complex.ofReal_pow, hreal]
  push_cast; ring

/-! ## 5. The ring hom phi : RElt -> C -/

noncomputable def evalKey (key : ℕ) (v : K16) : ℂ :=
  let cov := key % 16
  let ei := key / 16 % 2
  let e5 := key / 32 % 2
  let e1 := key / 64
  let base := evalK16 g0C v
  let scov := ((if cov % 2 = 1 then sVal 0 else 1) *
               (if (cov / 2) % 2 = 1 then sVal 1 else 1) *
               (if (cov / 4) % 2 = 1 then sVal 2 else 1) *
               (if (cov / 8) % 2 = 1 then sVal 3 else 1))
  base * scov * (iVal ^ ei) * (c5Val ^ e5) * (u1Val ^ e1)

noncomputable def phi (A : RElt) : ℂ :=
  (A.map fun p => evalKey p.1 p.2).sum

@[simp] theorem phi_nil : phi [] = 0 := rfl

theorem phi_rK (v : K16) : phi (rK v) = evalK16 g0C v := by
  simp [phi, rK, evalKey]

lemma evalKey_kadd_key (k : ℕ) (v w : K16) :
    evalKey k (kadd v w) = evalKey k v + evalKey k w := by
  unfold evalKey
  rw [evalK16_kadd]
  ring

@[simp] lemma phi_cons (p : ℕ × K16) (rest : RElt) :
    phi (p :: rest) = evalKey p.1 p.2 + phi rest := by
  simp [phi]

lemma evalK16_of_isZeroK (g : ℂ) :
    ∀ (v : List ℚ), isZeroK v = true → evalK16 g v = 0 := by
  intro v
  induction' v with a v' ih
  · intro _; simp [evalK16]
  · intro h
    simp only [isZeroK, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hv'⟩ := h
    rw [evalK16_cons, ha, ih (by simpa [isZeroK] using hv')]; simp

lemma evalKey_of_isZeroK (k : ℕ) (v : K16) (h : isZeroK v = true) :
    evalKey k v = 0 := by
  simp only [evalKey, evalK16_of_isZeroK g0C v h, zero_mul]

/-- The linchpin: inserting one (key, value) into a sorted assoc list adds its
    `evalKey` to `phi`, regardless of whether it lands fresh, merges, or cancels. -/
lemma phi_insertAdd (acc : RElt) (k : ℕ) (v : K16) :
    phi (insertAdd acc k v) = phi acc + evalKey k v := by
  induction' acc with p rest ih
  · simp only [insertAdd]
    split
    · rename_i hz; rw [evalKey_of_isZeroK k v hz]; simp
    · simp
  · obtain ⟨k', v'⟩ := p
    simp only [insertAdd]
    split
    · -- k < k'
      split
      · rename_i hz; rw [evalKey_of_isZeroK k v hz]; simp
      · simp only [phi_cons]; ring
    · split
      · -- k == k'
        rename_i hkk
        have hk : k = k' := by simpa using hkk
        split
        · -- isZeroK (kadd v' v): the merged entry cancels
          rename_i hw
          have hz : evalKey k' v' + evalKey k' v = 0 := by
            rw [← evalKey_kadd_key]; exact evalKey_of_isZeroK k' (kadd v' v) hw
          simp only [phi_cons]; subst hk; linear_combination -hz
        · -- merged entry survives
          rename_i hw
          simp only [phi_cons]; subst hk
          rw [evalKey_kadd_key]; ring
      · -- k ≠ k', recurse into the tail
        simp only [phi_cons]; rw [ih]; ring

lemma phi_foldl_insertAdd (L : List (ℕ × K16)) (acc : RElt) :
    phi (L.foldl (fun a p => insertAdd a p.1 p.2) acc)
      = phi acc + (L.map (fun p => evalKey p.1 p.2)).sum := by
  induction' L with p L' ih generalizing acc
  · simp
  · simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (insertAdd acc p.1 p.2), phi_insertAdd]
    ring

/-- phi respects addition: phi(radd A B) = phi A + phi B. -/
theorem phi_radd (A B : RElt) : phi (radd A B) = phi A + phi B := by
  unfold radd
  rw [phi_foldl_insertAdd]
  rfl

/-! ### The unreduced monomial value and key decoding -/

/-- Cover-phase product for a 4-bit cover mask. -/
noncomputable def scov (cov : ℕ) : ℂ :=
  (if cov % 2 = 1 then sVal 0 else 1) * (if (cov / 2) % 2 = 1 then sVal 1 else 1) *
  (if (cov / 4) % 2 = 1 then sVal 2 else 1) * (if (cov / 8) % 2 = 1 then sVal 3 else 1)

/-- Value of a raw (possibly unreduced) monomial: coefficient · covers · i^ei · c5^e5 · u1^e1. -/
noncomputable def monVal (cov ei e5 e1 : ℕ) (c : K16) : ℂ :=
  evalK16 g0C c * scov cov * iVal ^ ei * c5Val ^ e5 * u1Val ^ e1

lemma evalKey_eq_monVal (key : ℕ) (v : K16) :
    evalKey key v = monVal (key % 16) (key / 16 % 2) (key / 32 % 2) (key / 64) v := by
  simp only [evalKey, monVal, scov]

lemma encKey_decode (cov ei e5 e1 : ℕ) (hcov : cov < 16) (hei : ei < 2)
    (he5 : e5 < 2) (he1 : e1 < 2) :
    encKey cov ei e5 e1 % 16 = cov ∧ encKey cov ei e5 e1 / 16 % 2 = ei ∧
    encKey cov ei e5 e1 / 32 % 2 = e5 ∧ encKey cov ei e5 e1 / 64 = e1 := by
  unfold encKey; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

lemma evalKey_encKey (cov ei e5 e1 : ℕ) (c : K16) (hcov : cov < 16) (hei : ei < 2)
    (he5 : e5 < 2) (he1 : e1 < 2) :
    evalKey (encKey cov ei e5 e1) c = monVal cov ei e5 e1 c := by
  rw [evalKey_eq_monVal]
  obtain ⟨h1, h2, h3, h4⟩ := encKey_decode cov ei e5 e1 hcov hei he5 he1
  rw [h1, h2, h3, h4]

/-! ### Reduction soundness: each layer preserves the monomial value under phi -/

/-- c5-layer (red3): sum of the emitted canonical monomials equals the input value. -/
lemma red3_sum (cov ei e5 e1 : ℕ) (c : K16) (hcov : cov < 16) (hei : ei < 2)
    (he1 : e1 < 2) (he5 : e5 < 3) :
    ((red3 (cov, ei, e5, e1, c)).map (fun p => evalKey p.1 p.2)).sum
      = monVal cov ei e5 e1 c := by
  simp only [red3]
  split_ifs with h
  · have he : e5 = 2 := by omega
    subst he
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evalKey_encKey cov ei 1 e1 _ hcov hei (by norm_num) he1,
        evalKey_encKey cov ei 0 e1 _ hcov hei (by norm_num) he1]
    simp only [monVal, evalK16_kscale, evalK16_kmul]
    push_cast
    linear_combination
      (-(evalK16 g0C c * scov cov * iVal ^ ei * u1Val ^ e1)) * c5Val_sq
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [evalKey_encKey cov ei e5 e1 _ hcov hei (by omega) he1]

/-- i-layer (red2) then c5-layer: preserves value while reducing ei mod 2. -/
lemma red2_red3_sum (cov ei e5 e1 : ℕ) (c : K16) (hcov : cov < 16) (hei : ei < 4)
    (he5 : e5 < 3) (he1 : e1 < 2) :
    ((red3 (red2 (cov, ei, e5, e1, c))).map (fun p => evalKey p.1 p.2)).sum
      = monVal cov ei e5 e1 c := by
  simp only [red2]
  split_ifs with h
  · rw [red3_sum cov (ei - 2) e5 e1 (kscale (-1) c) hcov (by omega) he1 he5]
    simp only [monVal, evalK16_kscale]
    have hpow : iVal ^ ei = iVal ^ (ei - 2) * iVal ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, iVal_sq]
    push_cast; ring
  · rw [red3_sum cov ei e5 e1 c hcov (by omega) he1 he5]

/-- u1-layer (red1) composed with the rest: the whole `contrib` preserves the value. -/
lemma contrib_sound (cov ei e5 e1 : ℕ) (c : K16) (hcov : cov < 16) (hei : ei < 3)
    (he5 : e5 < 3) (he1 : e1 < 3) :
    ((contrib cov ei e5 e1 c).map (fun p => evalKey p.1 p.2)).sum = monVal cov ei e5 e1 c := by
  simp only [contrib, red1]
  split_ifs with h
  · have he : e1 = 2 := by omega
    subst he
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.sum_append]
    rw [red2_red3_sum cov ei e5 0 (kmul c C2H) hcov (by omega) he5 (by norm_num),
        red2_red3_sum cov (ei + 1) e5 0 (kmul c S2H) hcov (by omega) he5 (by norm_num)]
    simp only [monVal, evalK16_kmul, pow_succ, pow_zero, mul_one]
    linear_combination
      (-(evalK16 g0C c * scov cov * c5Val ^ e5 * iVal ^ ei)) * u1Val_sq
  · simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [red2_red3_sum cov ei e5 e1 c hcov (by omega) he5 (by omega)]

/-! ### Cover correction and the monomial product identity -/

/-- `covCorr` folds `kmul` by `covK b` over the set bits; under evalK16 that is a product. -/
lemma evalK16_covCorr (m : ℕ) (c : K16) :
    evalK16 g0C (covCorr m c) = evalK16 g0C c *
      ((if (m >>> 0) &&& 1 == 1 then evalK16 g0C (covK 0) else 1) *
       (if (m >>> 1) &&& 1 == 1 then evalK16 g0C (covK 1) else 1) *
       (if (m >>> 2) &&& 1 == 1 then evalK16 g0C (covK 2) else 1) *
       (if (m >>> 3) &&& 1 == 1 then evalK16 g0C (covK 3) else 1)) := by
  unfold covCorr
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil]
  split_ifs <;> (try simp only [evalK16_kmul]) <;> ring

/-- The pure cover identity: the XOR cover times the shared-bit (AND) squared covers
    equals the product of the two individual covers. Proven by exhausting the 4 bits of
    each 4-bit mask; `ring` only ever sees the four `sVal` atoms, so it stays cheap. -/
lemma cover_identity (A B : ℕ) (hA : A < 16) (hB : B < 16) :
    scov (A ^^^ B) *
      ((if ((A &&& B) >>> 0) &&& 1 == 1 then evalK16 g0C (covK 0) else 1) *
       (if ((A &&& B) >>> 1) &&& 1 == 1 then evalK16 g0C (covK 1) else 1) *
       (if ((A &&& B) >>> 2) &&& 1 == 1 then evalK16 g0C (covK 2) else 1) *
       (if ((A &&& B) >>> 3) &&& 1 == 1 then evalK16 g0C (covK 3) else 1))
    = scov A * scov B := by
  have s0 := sVal_sq 0 (by norm_num)
  have s1 := sVal_sq 1 (by norm_num)
  have s2 := sVal_sq 2 (by norm_num)
  have s3 := sVal_sq 3 (by norm_num)
  interval_cases A <;> interval_cases B <;>
    simp only [scov, ← s0, ← s1, ← s2, ← s3] <;> norm_num <;> ring

/-- The pointwise product law: the reduced monomial for the product of two ring
    monomials equals the product of their `evalKey`s. -/
lemma monVal_product (ka kb : ℕ) (va vb : K16) :
    monVal ((ka % 16) ^^^ (kb % 16)) (ka / 16 % 2 + kb / 16 % 2)
      (ka / 32 % 2 + kb / 32 % 2) (ka / 64 + kb / 64)
      (covCorr ((ka % 16) &&& (kb % 16)) (kmul va vb))
    = evalKey ka va * evalKey kb vb := by
  rw [evalKey_eq_monVal ka va, evalKey_eq_monVal kb vb]
  simp only [monVal, evalK16_covCorr, evalK16_kmul, pow_add]
  have key := cover_identity (ka % 16) (kb % 16)
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  linear_combination (evalK16 g0C va * evalK16 g0C vb *
      iVal ^ (ka / 16 % 2) * iVal ^ (kb / 16 % 2) *
      c5Val ^ (ka / 32 % 2) * c5Val ^ (kb / 32 % 2) *
      u1Val ^ (ka / 64) * u1Val ^ (kb / 64)) * key

/-- phi respects multiplication: phi(rmul A B) = phi A * phi B. -/
theorem phi_rmul (A B : RElt) : phi (rmul A B) = phi A * phi B := by
  sorry

/-- phi respects conjugation: phi(rconj A) = star (phi A). -/
theorem phi_rconj (A : RElt) : phi (rconj A) = star (phi A) := by
  sorry

/-! ## 6. The SIC-POVM fiducial -/

noncomputable def psi : Fin 12 → ℂ := fun k => phi (rZ k.val)

theorem norm_sq_eq_one : wh_normSq 12 psi = 1 := by
  sorry

theorem equiangular : ∀ (a b : Fin 12), (a, b) ≠ (0, 0) →
    ((12 : ℝ) + 1) * ‖wh_inner 12 psi (D_ah 12 a b 0 psi)‖ ^ 2 = 1 := by
  sorry

theorem d12_sic_exists : IsSICPOVM 12 psi :=
  { norm_eq := norm_sq_eq_one
    equiangular := equiangular }

theorem crystal_forces_d12_sic : SICPOVM_Exists 12 := by
  refine ⟨psi, d12_sic_exists⟩

end
end SIC.D12.Embedding
