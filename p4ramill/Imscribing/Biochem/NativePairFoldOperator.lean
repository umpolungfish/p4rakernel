import Imscribing.Biochem.PrimaLogicaMechanicalGlut

/-! Exact joint-interaction closure for an ordered pair of native SIXTEEN_3
residue states, with the coefficient address carried through FOUR's character
frame. -/
namespace Imscribing.PrimaLogica.MechanicalGlut.LatticeInteraction

open Lean Imscribing.Paraconsistent

abbrev PairResponse := Sixteen3 → Sixteen3 → ℝ

/-- Apply the native four-membership Möbius operator to the left residue. -/
noncomputable def interactLeft (f : PairResponse) : PairResponse :=
  fun s t => interactions (fun s' => f s' t) s

/-- Apply the native four-membership Möbius operator to the right residue. -/
noncomputable def interactRight (f : PairResponse) : PairResponse :=
  fun s t => interactions (fun t' => f s t') t

/-- The full 256-state residue-pair interaction decomposition: eight
membership differences, four at each source-addressed residue. -/
noncomputable def pairInteractions (f : PairResponse) : PairResponse :=
  interactRight (interactLeft f)

noncomputable def reconstructLeft (f : PairResponse) : PairResponse :=
  fun s t => reconstruct (fun s' => f s' t) s

noncomputable def reconstructRight (f : PairResponse) : PairResponse :=
  fun s t => reconstruct (fun t' => f s t') t

/-- Rebuild the pair response from its eight-difference coefficients. -/
noncomputable def reconstructPair (f : PairResponse) : PairResponse :=
  reconstructLeft (reconstructRight f)

theorem reconstructPair_pairInteractions (f : PairResponse) :
    reconstructPair (pairInteractions f) = f := by
  funext s t
  simp [reconstructPair, pairInteractions, reconstructLeft, reconstructRight,
    interactLeft, interactRight, reconstruct_interactions]

theorem pairInteractions_reconstructPair (f : PairResponse) :
    pairInteractions (reconstructPair f) = f := by
  funext s t
  simp [reconstructPair, pairInteractions, reconstructLeft, reconstructRight,
    interactLeft, interactRight, interactions_reconstruct]

/-- The affine tetrahedral address of one full support subset. Cardinality
retains the constant character while the three coordinates retain FOUR's
nontrivial characters. -/
def supportFrameAddress (s : Sixteen3) : ℕ × (ℚ × ℚ × ℚ) :=
  (s.hasN.toNat + s.hasT.toNat + s.hasF.toNat + s.hasB.toNat,
   (if s.hasN then NativeFrame.vertex .N else (0,0,0)) +
   (if s.hasT then NativeFrame.vertex .T else (0,0,0)) +
   (if s.hasF then NativeFrame.vertex .F else (0,0,0)) +
   (if s.hasB then NativeFrame.vertex .B else (0,0,0)))

/-- The affine tetrahedral address distinguishes all sixteen support subsets,
including the empty and complete supports whose vertex sums both vanish. -/
theorem supportFrameAddress_injective : Function.Injective supportFrameAddress := by
  intro s t h
  rcases s with ⟨sn,st,sf,sb⟩
  rcases t with ⟨tn,tt,tf,tb⟩
  simp only [supportFrameAddress, Prod.mk.injEq] at h
  rcases h with ⟨hc,hv⟩
  cases sn <;> cases st <;> cases sf <;> cases sb <;>
    cases tn <;> cases tt <;> cases tf <;> cases tb
  all_goals simp_all [NativeFrame.vertex, NativeFrame.truthCharacter,
    NativeFrame.falseCharacter, Imscribing.Paraconsistent.designated,
    Imscribing.Paraconsistent.bnot]
  all_goals norm_num at *

/-- A pair coefficient address is retained by the product of the two affine
tetrahedral support addresses. -/
def pairFrameAddress (s t : Sixteen3) :
    (ℕ × (ℚ × ℚ × ℚ)) × (ℕ × (ℚ × ℚ × ℚ)) :=
  (supportFrameAddress s, supportFrameAddress t)

theorem pairFrameAddress_injective {s₁ t₁ s₂ t₂ : Sixteen3}
    (h : pairFrameAddress s₁ t₁ = pairFrameAddress s₂ t₂) :
    s₁ = s₂ ∧ t₁ = t₂ := by
  simp only [pairFrameAddress, Prod.mk.injEq] at h
  exact ⟨supportFrameAddress_injective h.1, supportFrameAddress_injective h.2⟩

/-- Contract one lattice join/meet pair in the affine FOUR frame. The
constant character (support cardinality) wedges with the three tetrahedral
characters, so no character coordinate is silently discarded. -/
def affineFrameWedge (a b : Sixteen3) : ℚ × ℚ × ℚ :=
  let (ra, pa) := supportFrameAddress a
  let (rb, pb) := supportFrameAddress b
  ((ra : ℚ) * pb.1 - (rb : ℚ) * pa.1,
   (ra : ℚ) * pb.2.1 - (rb : ℚ) * pa.2.1,
   (ra : ℚ) * pb.2.2 - (rb : ℚ) * pa.2.2)

def addFrameVectors (a b : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- The one pair contraction retains all three native SIXTEEN₃ orders:
information, truth, and falsity, each as its join/meet boundary in FOUR's
affine character frame. -/
def pairContextContraction (s t : Sixteen3) : ℚ × ℚ × ℚ :=
  addFrameVectors
    (addFrameVectors
      (affineFrameWedge (Sixteen3.join_i s t) (Sixteen3.meet_i s t))
      (affineFrameWedge (Sixteen3.join_t s t) (Sixteen3.meet_t s t)))
    (affineFrameWedge (Sixteen3.join_f s t) (Sixteen3.meet_f s t))

/-- Native pair radial target from the sum of the two residue support
quadratics. It is exactly the inverse-stiffness one-step value first/k. -/
noncomputable def pairRadialTarget (s t : Sixteen3) : ℝ :=
  let ps : ℝ := NativeGlut.positive s
  let ns : ℝ := NativeGlut.negative s
  let pt : ℝ := NativeGlut.positive t
  let nt : ℝ := NativeGlut.negative t
  let k := ps + ns + pt + nt
  let first := ns * (ps + ns) + nt * (pt + nt)
  if hk : k = 0 then 0 else first / k

/-! ### Whole-chain composition

The pair contraction composes by tensor incidence over every unordered
residue pair. Each residue accumulates the stiffness and first moment of its
incident pair terms; the single chain contraction is the corresponding
source-derived affine minimizer. No pair output is fed serially into the
next pair, so the result is independent of pair enumeration. -/

abbrev Peptide20 := Fin 20 → Sixteen3
abbrev Backbone20 := Fin 20 → ℝ

noncomputable def pairStiffness (s t : Sixteen3) : ℝ :=
  (NativeGlut.positive s : ℝ) + NativeGlut.negative s +
    NativeGlut.positive t + NativeGlut.negative t

noncomputable def pairFirstMoment (s t : Sixteen3) : ℝ :=
  (NativeGlut.negative s : ℝ) *
      (NativeGlut.positive s + NativeGlut.negative s) +
    NativeGlut.negative t *
      (NativeGlut.positive t + NativeGlut.negative t)

/-- Tensor the pair quadratics across the complete chain, retaining each
pair through its incidence at a residue. -/
noncomputable def chainStiffness (source : Peptide20) (i : Fin 20) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, pairStiffness (source i) (source j)

noncomputable def chainFirstMoment (source : Peptide20) (i : Fin 20) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, pairFirstMoment (source i) (source j)

/-- One simultaneous contraction of all 190 pair terms. The incoming
backbone is contracted once against the full source-derived chain tensor. -/
noncomputable def wholeChainContraction (source : Peptide20)
    (backbone : Backbone20) : Backbone20 := fun i =>
  let k := chainStiffness source i
  let first := chainFirstMoment source i
  if hk : k = 0 then backbone i else first / k

theorem wholeChainContraction_fixed (source : Peptide20)
    (backbone : Backbone20) :
    wholeChainContraction source (wholeChainContraction source backbone) =
      wholeChainContraction source backbone := by
  funext i
  simp only [wholeChainContraction]
  split
  · rfl
  · rename_i hk
    simp [hk]

/-- Apply that pair contraction once to the complete reconstructed joint
distribution. `pairInteractions` supplies the signed eight-difference
coefficients; `reconstructPair` restores every source state before the
single character-frame contraction. -/
noncomputable def oneShotPairContraction (coefficients : PairResponse) :
    ℝ × ℝ × ℝ :=
  Finset.univ.sum fun si : Fin 16 =>
    Finset.univ.sum fun ti : Fin 16 =>
      let s := Sixteen3.ofMask si.val
      let t := Sixteen3.ofMask ti.val
      let mass := reconstructPair coefficients s t
      let frame := pairContextContraction s t
      let radial := pairRadialTarget s t
      (mass * radial * (frame.1 : ℝ), mass * radial * (frame.2.1 : ℝ),
       mass * radial * (frame.2.2 : ℝ))

/-- Exact signed shell-channel contraction. The incidence weight records
which containing support families admit the addressed shell channel. -/
noncomputable def shellPushforward (weight : Fin 256 → Fin 16 → ℤ)
    (coefficients : Fin 256 → ℤ) (channel : Fin 16) : ℤ :=
  ∑ support, coefficients support * weight support channel

theorem shellPushforward_add (weight : Fin 256 → Fin 16 → ℤ)
    (a b : Fin 256 → ℤ) (channel : Fin 16) :
    shellPushforward weight (fun k => a k + b k) channel =
      shellPushforward weight a channel + shellPushforward weight b channel := by
  simp [shellPushforward, add_mul, Finset.sum_add_distrib]

/-- Grouping retained interaction shells cannot change the returned channel. -/
theorem shellPushforward_associative (weight : Fin 256 → Fin 16 → ℤ)
    (a b c : Fin 256 → ℤ) (channel : Fin 16) :
    shellPushforward weight (fun k => (a k + b k) + c k) channel =
      shellPushforward weight (fun k => a k + (b k + c k)) channel := by
  simp only [add_assoc]

/-- Move a spatial response through the incidence reconstruction without
collapsing its joint-state addresses to shell-channel marginals. The response
may depend on the full carried conformation. -/
theorem jointResponse_incidence_dual (incidence : Fin 256 → Fin 256 → ℝ)
    (coefficients response : Fin 256 → ℝ) :
    (∑ state, (∑ support, coefficients support * incidence support state) * response state) =
      ∑ support, coefficients support * (∑ state, incidence support state * response state) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Rational half-angle action on the plane normal to a retained bond.
The parameter is algebraic; no angle or trigonometric evaluation is needed. -/
noncomputable def rotationCos (t : ℝ) : ℝ := (1-t*t)/(1+t*t)
noncomputable def rotationSin (t : ℝ) : ℝ := (2*t)/(1+t*t)

theorem rational_rotation_unit (t : ℝ) :
    rotationCos t ^ 2 + rotationSin t ^ 2 = 1 := by
  have h : (1+t*t : ℝ) ≠ 0 := by nlinarith [sq_nonneg t]
  unfold rotationCos rotationSin
  field_simp
  <;> ring

theorem rational_rotation_preserves_norm (t x y : ℝ) :
    (rotationCos t*x-rotationSin t*y)^2 +
      (rotationSin t*x+rotationCos t*y)^2 = x^2+y^2 := by
  have h := rational_rotation_unit t
  calc
    _ = (rotationCos t^2+rotationSin t^2)*(x^2+y^2) := by ring
    _ = x^2+y^2 := by rw [h]; ring

/-- Total extension of the native support quadratic, including zero extents.
Its physical displacement interpretation remains an explicit model input. -/
noncomputable def sourceSupportPotential (s : Sixteen3) (q : ℝ) : ℝ :=
  let p : ℝ := NativeGlut.positive s
  let n : ℝ := NativeGlut.negative s
  p*q^2/2+n*(q-(p+n))^2/2

theorem sourceSupportPotential_moments (s : Sixteen3) (q : ℝ) :
    sourceSupportPotential s q =
      (((NativeGlut.positive s : ℝ)+NativeGlut.negative s)*q^2 -
       2*(NativeGlut.negative s : ℝ)*(NativeGlut.positive s+NativeGlut.negative s)*q +
       (NativeGlut.negative s : ℝ)*(NativeGlut.positive s+NativeGlut.negative s)^2)/2 := by
  unfold sourceSupportPotential
  push_cast
  ring

theorem sourceSupportPotential_derivative (s : Sixteen3) (q : ℝ) :
    HasDerivAt (sourceSupportPotential s)
      (((NativeGlut.positive s : ℝ)+NativeGlut.negative s)*q -
       (NativeGlut.negative s : ℝ)*(NativeGlut.positive s+NativeGlut.negative s)) q := by
  unfold sourceSupportPotential
  convert (((hasDerivAt_id q).pow 2).const_mul (NativeGlut.positive s : ℝ)).div_const 2 |>.add
    (((((hasDerivAt_id q).sub_const ((NativeGlut.positive s : ℝ)+NativeGlut.negative s)).pow 2).const_mul
      (NativeGlut.negative s : ℝ)).div_const 2) using 1 <;> simp only [id_eq] <;> push_cast <;> ring

/-- Native affine mechanical action at its inverse-stiffness step. -/
noncomputable def radialNest (k first q : ℝ) : ℝ := q-(k*q-first)/k

theorem radialNest_one_shot (k first q : ℝ) (hk : k ≠ 0) :
    radialNest k first q = first/k := by
  unfold radialNest
  field_simp
  <;> ring

theorem radialNest_idempotent (k first q : ℝ) (hk : k ≠ 0) :
    radialNest k first (radialNest k first q) = radialNest k first q := by
  rw [radialNest_one_shot k first _ hk, radialNest_one_shot k first _ hk]

/-- A source character winding supplies an algebraic unit direction directly.
The positive square root selects the source's oriented branch; an angle is
unnecessary for the backbone construction. -/
theorem sourceWinding_direction_unit (x y radius : ℝ)
    (hr : radius ≠ 0) (hs : radius^2 = x^2+y^2) :
    (x/radius)^2+(y/radius)^2 = 1 := by
  field_simp
  nlinarith

theorem sourceWinding_direction_pairing (x y radius : ℝ)
    (hr : radius ≠ 0) :
    (x/radius)*y = (y/radius)*x := by
  field_simp
  <;> ring

/-- Channel deformation plus the retained bank expressed in preference q.
The common source multiplicity can multiply this whole expression. -/
noncomputable def conditionalBankEnergy (p n d q : ℝ) : ℝ :=
  (p+n)*(d-q)^2/2+p*((p+n)*q^2/n-p*n)/2

theorem conditionalBank_completed_square (p n d q : ℝ)
    (hn : n ≠ 0) (hs : p+n ≠ 0) :
    conditionalBankEnergy p n d q - conditionalBankEnergy p n d (n*d/(p+n)) =
      (p+n)^2/(2*n)*(q-n*d/(p+n))^2 := by
  unfold conditionalBankEnergy
  field_simp
  <;> ring

theorem conditionalBank_minimum (p n d q : ℝ)
    (hn : 0 < n) (hs : p+n ≠ 0) :
    conditionalBankEnergy p n d (n*d/(p+n)) ≤ conditionalBankEnergy p n d q := by
  have h := conditionalBank_completed_square p n d q (ne_of_gt hn) hs
  have hc : 0 ≤ (p+n)^2/(2*n) := div_nonneg (sq_nonneg _) (by positivity)
  have hr := mul_nonneg hc (sq_nonneg (q-n*d/(p+n)))
  linarith

noncomputable def retainedClamp (lower upper x : ℝ) : ℝ :=
  max lower (min upper x)

theorem retainedClamp_idempotent (lower upper x : ℝ) (h : lower ≤ upper) :
    retainedClamp lower upper (retainedClamp lower upper x) = retainedClamp lower upper x := by
  have hl : lower ≤ retainedClamp lower upper x := le_max_left _ _
  have hu : retainedClamp lower upper x ≤ upper := max_le h (min_le_left _ _)
  change max lower (min upper (retainedClamp lower upper x)) = retainedClamp lower upper x
  rw [min_eq_right hu, max_eq_right hl]

theorem retainedClamp_distance (lower upper x q : ℝ)
    (hlu : lower ≤ upper) (hlq : lower ≤ q) (hqu : q ≤ upper) :
    (retainedClamp lower upper x-x)^2 ≤ (q-x)^2 := by
  by_cases hxl : x ≤ lower
  · have hc : retainedClamp lower upper x = lower := by
      simp [retainedClamp, min_eq_right (le_trans hxl hlu), max_eq_left hxl]
    rw [hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlq) (show 0 ≤ q+lower-2*x by linarith)]
  · by_cases hux : upper ≤ x
    · have hc : retainedClamp lower upper x = upper := by
        simp [retainedClamp, min_eq_left hux, max_eq_right hlu]
      rw [hc]
      nlinarith [mul_nonneg (sub_nonneg.mpr hqu) (show 0 ≤ 2*x-q-upper by linarith)]
    · have hc : retainedClamp lower upper x = x := by
        simp [retainedClamp, min_eq_right (le_of_not_ge hux),
          max_eq_right (le_of_not_ge hxl)]
      rw [hc]
      simpa using sq_nonneg (q-x)

theorem conditionalBank_constrained_minimum (p n d lower upper q : ℝ)
    (hn : 0 < n) (hs : p+n ≠ 0) (hlu : lower ≤ upper)
    (hlq : lower ≤ q) (hqu : q ≤ upper) :
    conditionalBankEnergy p n d (retainedClamp lower upper (n*d/(p+n))) ≤
      conditionalBankEnergy p n d q := by
  have ha := conditionalBank_completed_square p n d
    (retainedClamp lower upper (n*d/(p+n))) (ne_of_gt hn) hs
  have hb := conditionalBank_completed_square p n d q (ne_of_gt hn) hs
  have hd := retainedClamp_distance lower upper (n*d/(p+n)) q hlu hlq hqu
  have hc : 0 ≤ (p+n)^2/(2*n) := div_nonneg (sq_nonneg _) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hd hc
  linarith

end Imscribing.PrimaLogica.MechanicalGlut.LatticeInteraction
