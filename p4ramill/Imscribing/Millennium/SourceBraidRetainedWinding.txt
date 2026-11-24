import Imscribing.Millennium.SourceBraidSquareCollision

/-! Reversible source square winding on two retained residue banks.
This is a state-address equivalence, not an exact-expectation evaluator. -/
namespace Imscribing.SourceBraidRetainedWinding

def squareWinding (N : ℕ) : (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) where
  toFun xy := (xy.1, xy.2 + xy.1 ^ 2)
  invFun xy := (xy.1, xy.2 - xy.1 ^ 2)
  left_inv := by intro xy; ext <;> simp
  right_inv := by intro xy; ext <;> simp

theorem source_bank_preserved (N : ℕ) (xy : ZMod N × ZMod N) :
    (squareWinding N xy).1 = xy.1 := rfl

theorem zero_return_bank (N : ℕ) (x : ZMod N) :
    squareWinding N (x, 0) = (x, x ^ 2) := by
  simp [squareWinding]

theorem retained_addresses_injective (N : ℕ) :
    Function.Injective (fun x : ZMod N => squareWinding N (x, 0)) := by
  intro x y h
  exact congrArg Prod.fst h

theorem return_collision (N : ℕ) (x y : ZMod N) :
    (squareWinding N (x, 0)).2 = (squareWinding N (y, 0)).2 ↔
      x ^ 2 = y ^ 2 := by
  simp [squareWinding]

theorem inverse_recovers_banks (N : ℕ) (xy : ZMod N × ZMod N) :
    (squareWinding N).symm (squareWinding N xy) = xy :=
  (squareWinding N).symm_apply_apply xy

-- A partial observation can identify return addresses without identifying
-- the retained joint addresses. No quotient of the source bank is taken.
theorem opposite_returns (N : ℕ) (x : ZMod N) :
    (squareWinding N (x, 0)).2 = (squareWinding N (-x, 0)).2 := by
  simp [squareWinding]

/-- Joint amplitudes retain a separate source address for each return. -/
noncomputable def jointAmplitude {X Y : Type*} [DecidableEq Y]
    (f : X → Y) (x : X) (r : Y) : ℤ := if f x = r then 1 else 0

/-- Restrict observations to the return bank, without merging source amplitudes. -/
noncomputable def observedReturn {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) : Matrix Y Y ℤ :=
  fun r s => ∑ x, jointAmplitude f x r * jointAmplitude f x s

theorem observedReturn_eq_gram {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y) :
    observedReturn f = SourceBraidSquareCollision.returnGram f := by
  classical
  ext r s
  by_cases h : r = s
  · subst s
    simp only [observedReturn, jointAmplitude, SourceBraidSquareCollision.returnGram,
      Matrix.diagonal_apply_eq]
    have term (x : X) :
        (if f x = r then (1 : ℤ) else 0) * (if f x = r then 1 else 0) =
          if f x = r then 1 else 0 := by split_ifs <;> norm_num
    simp_rw [term]
    simp [Fintype.card_subtype]
  · simp only [observedReturn, SourceBraidSquareCollision.returnGram,
      Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : f x = r
    · have hs : f x ≠ s := by intro hs; exact h (hx.symm.trans hs)
      simp [jointAmplitude, hs]
    · simp [jointAmplitude, hx]

theorem observed_square_trace {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y) :
    Matrix.trace (observedReturn f * observedReturn f) =
      (Fintype.card {xy : X × X // f xy.1 = f xy.2} : ℤ) := by
  rw [observedReturn_eq_gram]
  exact SourceBraidSquareCollision.trace_return_square f

/-- Difference/sum chart on the composite source ring. Only an inverse of
two is required; a field structure or supplied prime factors are unnecessary. -/
def differenceSum {R : Type*} [CommRing R] (half : R)
    (hhalf : 2 * half = 1) : (R × R) ≃ (R × R) where
  toFun xy := (xy.1 - xy.2, xy.1 + xy.2)
  invFun uv := (half * (uv.1 + uv.2), half * (uv.2 - uv.1))
  left_inv := by
    intro xy
    apply Prod.ext <;> dsimp
    · linear_combination xy.1 * hhalf
    · linear_combination xy.2 * hhalf
  right_inv := by
    intro uv
    apply Prod.ext <;> dsimp
    · linear_combination uv.1 * hhalf
    · linear_combination uv.2 * hhalf

theorem differenceSum_collision {R : Type*} [CommRing R]
    (half : R) (hhalf : 2 * half = 1) (xy : R × R) :
    xy.1 ^ 2 = xy.2 ^ 2 ↔
      (differenceSum half hhalf xy).1 * (differenceSum half hhalf xy).2 = 0 := by
  change xy.1 ^ 2 = xy.2 ^ 2 ↔ (xy.1 - xy.2) * (xy.1 + xy.2) = 0
  rw [show (xy.1 - xy.2) * (xy.1 + xy.2) = xy.1 ^ 2 - xy.2 ^ 2 by ring]
  exact sub_eq_zero.symm

/-- Applied low square rows, retained without materializing an address table. -/
def partialSquare (x k : ℕ) : ℕ :=
  (x % 2^k)^2 + 2 * (x % 2^k) * 2^k * (x / 2^k)

theorem partialSquare_bank (x k : ℕ) :
    partialSquare x k + (x / 2^k)^2 * (2^k)^2 = x^2 := by
  have h := Nat.mod_add_div x (2^k)
  dsimp [partialSquare]
  conv_rhs => rw [← h]
  ring

theorem partialSquare_difference (x k : ℕ) :
    partialSquare x k = x^2 - (x / 2^k)^2 * (2^k)^2 := by
  have h := partialSquare_bank x k
  omega

/-- A return transformation independent of a retired source coordinate can
be pushed through that coordinate's contraction. Other coordinates remain
inside the arbitrary state and kernel functions. -/
theorem last_use_contraction {E R S : Type*} [Fintype E] [Fintype R]
    (state : E → R → ℤ) (kernel : R → S → ℤ) (s : S) :
    (∑ e, ∑ r, state e r * kernel r s) =
      ∑ r, (∑ e, state e r) * kernel r s := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]

/-- Arithmetic edge used by the native FOUR source image. This acts on the
carried square and address, not on a table of return rails. -/
def arithmeticEdge (digit : ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  (16*state.1 + 8*digit*state.2 + digit^2, 4*state.2+digit)

theorem arithmeticEdge_square (digit x : ℕ) :
    arithmeticEdge digit (x^2,x) = ((4*x+digit)^2,4*x+digit) := by
  apply Prod.ext <;> dsimp [arithmeticEdge] <;> ring

def arithmeticImage : List ℕ → ℕ × ℕ → ℕ × ℕ
  | [], state => state
  | digit::digits, state => arithmeticImage digits (arithmeticEdge digit state)

theorem arithmeticImage_square (digits : List ℕ) (x : ℕ) :
    (arithmeticImage digits (x^2,x)).1 =
      (arithmeticImage digits (x^2,x)).2^2 := by
  induction digits generalizing x with
  | nil => rfl
  | cons d ds ih =>
    simp only [arithmeticImage, arithmeticEdge_square]
    exact ih (4*x+d)

/-- Exact elimination of a complete linear zero-product fibre. The source
modulus need not be prime and no factor labels are supplied. -/
theorem zero_product_fibre_iff (N a b : ℕ) (hN : 0 < N) :
    N ∣ a*b ↔ N / Nat.gcd a N ∣ b := by
  let g := Nat.gcd a N
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hN
  have ha : g * (a/g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a N)
  have hn : g * (N/g) = N := Nat.mul_div_cancel' (Nat.gcd_dvd_right a N)
  have hc : Nat.Coprime (N/g) (a/g) := (Nat.coprime_div_gcd_div_gcd hg).symm
  constructor
  · intro h
    have h' : g*(N/g) ∣ g*((a/g)*b) := by
      simpa only [← Nat.mul_assoc, ha, hn] using h
    exact hc.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hg).mp h')
  · intro h
    have h' : N/g ∣ (a/g)*b := dvd_mul_of_dvd_right h (a/g)
    have h'' := Nat.mul_dvd_mul_left g h'
    simpa only [← Nat.mul_assoc, ha, hn] using h''

/-- The compact arithmetic fibre retains exactly gcd(a,N) addressed members,
including the complete fibre at a=0. No residue enumeration is needed to
construct the equivalence. -/
def zeroProductFibreEquiv (N a : ℕ) (hN : 0 < N) :
    {b : Fin N // N ∣ a*b.val} ≃ Fin (Nat.gcd a N) := by
  let g := Nat.gcd a N
  let step := N/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hN
  have hs : 0 < step := Nat.div_pos (Nat.gcd_le_right a hN) hg
  have hn : step*g=N := Nat.div_mul_cancel (Nat.gcd_dvd_right a N)
  refine {
    toFun := fun b => ⟨b.val.val/step, ?_⟩
    invFun := fun t => ⟨⟨step*t.val, ?_⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (Nat.div_lt_iff_lt_mul hs).mpr
    change b.val.val < g*step
    rw [Nat.mul_comm g step, hn]
    exact b.val.isLt
  · change step*t.val < N
    exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left t.isLt hs) hn
  · exact (zero_product_fibre_iff N a (step*t.val) hN).mpr (dvd_mul_right step t.val)
  · intro b
    apply Subtype.ext
    apply Fin.ext
    exact Nat.mul_div_cancel' ((zero_product_fibre_iff N a b.val.val hN).mp b.property)
  · intro t
    apply Fin.ext
    exact Nat.mul_div_cancel_left t.val hs

theorem zero_product_fibre_card (N a : ℕ) (hN : 0 < N) :
    Fintype.card {b : Fin N // N ∣ a*b.val} = Nat.gcd a N := by
  classical
  exact (Fintype.card_congr (zeroProductFibreEquiv N a hN)).trans (Fintype.card_fin _)

/-- Removing both axes of the complete zero-product relation leaves only
proper gcd fibres. This is a projection on the family, not a choice function. -/
theorem nonzero_zero_product_proper (N a b : ℕ) (hN : 0 < N)
    (ha : 0 < a) (haN : a < N) (hb : 0 < b) (hbN : b < N)
    (hzero : N ∣ a*b) : 1 < Nat.gcd a N ∧ Nat.gcd a N < N := by
  have hg := Nat.gcd_pos_of_pos_right a hN
  have hgle := Nat.gcd_le_right a hN
  have hnotone : Nat.gcd a N ≠ 1 := by
    intro h
    have hdiv := (zero_product_fibre_iff N a b hN).mp hzero
    rw [h, Nat.div_one] at hdiv
    exact (not_le_of_gt hbN) (Nat.le_of_dvd hb hdiv)
  have hnotN : Nat.gcd a N ≠ N := by
    intro h
    have hdiv := Nat.gcd_dvd_left a N
    rw [h] at hdiv
    exact (not_le_of_gt haN) (Nat.le_of_dvd ha hdiv)
  omega

def properAxisMask (N a b : ℕ) : ℤ :=
  if 0<a ∧ a<N ∧ 0<b ∧ b<N ∧ N ∣ a*b then 1 else 0

theorem properAxisMask_idempotent (N a b : ℕ) :
    properAxisMask N a b * properAxisMask N a b = properAxisMask N a b := by
  unfold properAxisMask
  split_ifs <;> norm_num

/-- The native reader retains only the zero-arm guard for reverse recovery.
The existential message supplies the other arm when that guard is false. -/
theorem existential_choice_guard (low high : Bool) (supported : low || high = true) :
    (if !low then high else low) = true := by
  cases low <;> cases high <;> simp_all

end Imscribing.SourceBraidRetainedWinding

#print axioms Imscribing.SourceBraidRetainedWinding.inverse_recovers_banks
#print axioms Imscribing.SourceBraidRetainedWinding.retained_addresses_injective
#print axioms Imscribing.SourceBraidRetainedWinding.partialSquare_difference
#print axioms Imscribing.SourceBraidRetainedWinding.last_use_contraction
#print axioms Imscribing.SourceBraidRetainedWinding.arithmeticImage_square
#print axioms Imscribing.SourceBraidRetainedWinding.zero_product_fibre_iff
#print axioms Imscribing.SourceBraidRetainedWinding.zero_product_fibre_card
#print axioms Imscribing.SourceBraidRetainedWinding.nonzero_zero_product_proper
#print axioms Imscribing.SourceBraidRetainedWinding.properAxisMask_idempotent
#print axioms Imscribing.SourceBraidRetainedWinding.existential_choice_guard
