import Mathlib
import Imscribing.Millennium.WKExpand
open Imscribing.Millennium.WKExpand
open Erdos220
open scoped ComplexConjugate
noncomputable section

variable (d : ℕ) [NeZero d]
local notation "w" => fourierRoot d

def corr (N : ZMod d → ℝ) (m : ZMod d) : ℝ :=
  ∑ l : ZMod d, N (m + l) * N l

/-- Wiener-Khinchin: star(nu_b)*nu_b = sum_m corr(m) w^{bm}. -/
theorem wk_full (N : ZMod d → ℝ) (b : ZMod d) :
    star (nu d N b) * nu d N b =
      ∑ m : ZMod d, ((corr d N m : ℝ) : ℂ) * w ^ (b * m).val := by
  rw [wk_expand]

  -- 1. w^d = 1
  have exp_pow_nat : ∀ (z : ℂ) (n : ℕ), Complex.exp z ^ n = Complex.exp ((n : ℂ) * z) := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, Complex.exp_add]
  have hwd : w ^ d = 1 := by
    simp only [fourierRoot, exp_pow_nat]
    have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    rw [mul_comm, div_mul_cancel₀ _ hd]
    exact Complex.exp_eq_one_iff.mpr ⟨1, by ring⟩

  -- 2. w^(n % d) = w^n
  have hmod : ∀ n : ℕ, w ^ (n % d) = w ^ n := by
    intro n
    have h2 : w ^ n = w ^ (d * (n / d) + n % d) := by
      rw [Nat.div_add_mod n d]
    rw [h2, pow_add, pow_mul, hwd, one_pow, one_mul]

  -- 3. w^((u+v).val) = w^u.val * w^v.val
  have hmul : ∀ u v : ZMod d, w ^ (u + v).val = w ^ u.val * w ^ v.val := by
    intro u v
    rw [ZMod.val_add, hmod, pow_add]

  -- 4. star(w)^(b*l) * w^(b*(l+m)) = w^(b*m)
  have hpow : ∀ l m : ZMod d, (star w) ^ (b*l).val * w ^ (b*(l + m)).val = w ^ (b*m).val := by
    intro l m
    have hsp : (star w) ^ (b*l).val * w ^ (b*l).val = 1 := by
      rw [← mul_pow, fourierRoot_star_mul d (NeZero.pos d), one_pow]
    have hsplit : w ^ (b*(l + m)).val = w ^ (b*l).val * w ^ (b*m).val := by
      rw [mul_add, hmul]
    rw [hsplit]
    have hre : (star w) ^ (b*l).val * (w ^ (b*l).val * w ^ (b*m).val)
        = w ^ (b*m).val * ((star w) ^ (b*l).val * w ^ (b*l).val) := by ring
    rw [hre, hsp, mul_one]

  -- 5. Key algebraic identity for the summand
  have key : ∀ m l : ZMod d,
      ((N l : ℝ) : ℂ) * (star w) ^ (b*l).val * ((N (l + m) : ℝ) : ℂ) * w ^ (b*(l + m)).val
      = ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ) * w ^ (b*m).val := by
    intro m l
    calc ((N l : ℝ) : ℂ) * (star w) ^ (b*l).val * ((N (l + m) : ℝ) : ℂ) * w ^ (b*(l + m)).val
        _ = ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ) * ((star w) ^ (b*l).val * w ^ (b*(l + m)).val) := by ring
        _ = ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ) * w ^ (b*m).val := by rw [hpow l m]

  -- 6. Reindexing helpers (inline structures ensure projections reduce definitionally)
  have htransP : ∀ (l : ZMod d) (f : ZMod d → ℂ),
      (∑ x : ZMod d, f x) = (∑ j : ZMod d, f (j + l)) := by
    intro l f
    exact Fintype.sum_equiv
      { toFun := fun x => x - l, invFun := fun x => x + l,
        left_inv := by
          intro x
          simp [sub_add_cancel]
        right_inv := by
          intro x
          simp [sub_add_cancel] }
      f (fun m => f (m + l)) (fun x => by
        show f x = f ((x - l) + l)
        rw [sub_add_cancel])

  have htransI : ∀ (k : ZMod d) (f : ZMod d → ℂ),
      (∑ x : ZMod d, f x) = (∑ m : ZMod d, f (k - m)) := by
    intro k f
    exact Fintype.sum_equiv
      { toFun := fun x => k - x, invFun := fun x => k - x,
        left_inv := by
          intro x
          simp [sub_sub_cancel]
        right_inv := by
          intro x
          simp [sub_sub_cancel] }
      f (fun m => f (k - m)) (fun x => by
        show f x = f (k - (k - x))
        rw [sub_sub_cancel])

  -- 7. Main calculation
  calc (∑ k : ZMod d, ∑ l : ZMod d,
          ((N l : ℝ) : ℂ) * (star w) ^ (b*l).val * ((N k : ℝ) : ℂ) * w ^ (b*k).val)
      _ = ∑ k : ZMod d, ∑ m : ZMod d,
          ((N (k - m) : ℝ) : ℂ) * (star w) ^ (b*(k - m)).val * ((N k : ℝ) : ℂ) * w ^ (b*k).val := by
        apply Finset.sum_congr rfl
        intro k hk
        exact htransI k (fun x => ((N x : ℝ) : ℂ) * (star w) ^ (b*x).val * ((N k : ℝ) : ℂ) * w ^ (b*k).val)
      _ = ∑ m : ZMod d, ∑ k : ZMod d,
          ((N (k - m) : ℝ) : ℂ) * (star w) ^ (b*(k - m)).val * ((N k : ℝ) : ℂ) * w ^ (b*k).val := by
        rw [Finset.sum_comm]
      _ = ∑ m : ZMod d, ∑ j : ZMod d,
          ((N j : ℝ) : ℂ) * (star w) ^ (b*j).val * ((N (j + m) : ℝ) : ℂ) * w ^ (b*(j + m)).val := by
        apply Finset.sum_congr rfl
        intro m hm
        have hcancel : ∀ z : ZMod d, (z + m) - m = z := by
          intro z
          simp
        rw [htransP m (fun x => ((N (x - m) : ℝ) : ℂ) * (star w) ^ (b*(x - m)).val * ((N x : ℝ) : ℂ) * w ^ (b*x).val)]
        simp only [hcancel]
      _ = ∑ m : ZMod d, ∑ l : ZMod d,
          ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ) * w ^ (b*m).val := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro j hj
        rw [key m j]
      _ = ∑ m : ZMod d, ((corr d N m : ℝ) : ℂ) * w ^ (b*m).val := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Finset.sum_mul Finset.univ (fun l : ZMod d => ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ)) (w ^ (b * m).val)]
        have hcorr : (∑ l : ZMod d, ((N l : ℝ) : ℂ) * ((N (l + m) : ℝ) : ℂ)) = ((corr d N m : ℝ) : ℂ) := by
          simp only [corr]
          push_cast
          exact Finset.sum_congr rfl fun l _ => by
            rw [congrArg N (add_comm l m), mul_comm]
        rw [hcorr]
