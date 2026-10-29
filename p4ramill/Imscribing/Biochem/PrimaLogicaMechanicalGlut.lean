import Mathlib
import Imscribing.Paraconsistent.PrimaLogicaWinding

/-!
# Prima Logica — faithful logical-to-mechanical glut realization

A conditional, conservative mechanical realization of SIXTEEN_3 positive-and-negative support.

No proof below identifies logical contradiction with energy *without a bridge*.
The bridge `MechanicalEncoding.faithfulBoth` is an explicit physical realization
condition; it is not derived from FDE or from winding alone.

Model: two positive-stiffness quadratic potentials with distinct rest positions.
Release: detach the second potential while retaining the first, at the held
position. The available post-release energy is the retained first potential
above its zero minimum. A productive output assumes an efficiency 0 < eta <= 1.

Requires Mathlib and the Imscribing fork. Build this module and its audit with
`lake build Imscribing.Biochem.PrimaLogicaMechanicalGlut
Imscribing.Biochem.PrimaLogicaMechanicalGlutAudit` from the project root.
-/

namespace Imscribing.PrimaLogica.MechanicalGlut

open Lean Imscribing.PrimaLogica Imscribing.NSReentry Imscribing.Paraconsistent

/-! ## Explicit retraction: FOUR to SIXTEEN_3 and back -/

/-- Singleton embedding into the native carrier, not completion of a register. -/
def delta : Belnap → Sixteen3
  | .N => onlyN
  | .T => onlyT
  | .F => onlyF
  | .B => onlyB

/-- Positive and negative evidential supports aggregated over a SIXTEEN_3
    register. The independent N-membership is retained in the register but
    necessarily forgotten by the projection back to FOUR. -/
def supportPlus (s : Sixteen3) : Bool := s.hasT || s.hasB
def supportMinus (s : Sixteen3) : Bool := s.hasF || s.hasB

/-- Both in the FDE sense, including the `{T,F}` register even when `hasB=false`. -/
def IsBoth (s : Sixteen3) : Prop :=
  supportPlus s = true ∧ supportMinus s = true

/-- Canonical aggregate-support projection; not an isomorphism of trilattices.
    For example, both `{T,F}` and `{B}` project to Belnap.B. -/
def mu (s : Sixteen3) : Belnap :=
  if supportPlus s then
    if supportMinus s then .B else .T
  else if supportMinus s then .F else .N

/-- The requested split/retraction equation (μ ∘ δ = id on FOUR). -/
theorem mu_delta_id (v : Belnap) : mu (delta v) = v := by
  cases v <;> rfl

/-- The reverse is *not* the identity: full information collapses to B. -/
theorem mu_complete : mu complete = Belnap.B := rfl

theorem delta_mu_complete_ne_complete : delta (mu complete) ≠ complete := by
  decide

/-- Separate T and F evidence need not contain the singleton B member. -/
def separatedBoth : Sixteen3 :=
  Sixteen3.ofBelnap false true true false

theorem separatedBoth_isBoth : IsBoth separatedBoth := by
  constructor <;> rfl

theorem separatedBoth_lacks_B : separatedBoth.hasB = false := rfl

theorem mu_separatedBoth : mu separatedBoth = Belnap.B := rfl

/-- A winding completion yields both positive and negative aggregate support. -/
theorem winding_four_isBoth (s : Sixteen3) :
    IsBoth (wind (wind (wind (wind s)))) := by
  rw [wind_four_from_any]
  constructor <;> rfl

/-- Fourfold Inclosure followed by evidence projection returns FOUR.B. -/
theorem mu_after_winding (s : Sixteen3) :
    mu (wind (wind (wind (wind s)))) = Belnap.B := by
  rw [wind_four_from_any]
  rfl

/-! ## Mechanical theorem, independent of logical interpretation -/

/-- A concrete pair of incompatible, positive-stiffness preferences. -/
structure MechanicalGlut where
  k1 : ℝ
  k2 : ℝ
  a : ℝ
  b : ℝ
  k1_pos : 0 < k1
  k2_pos : 0 < k2
  mismatch : a ≠ b

namespace MechanicalGlut

/-- Held energy (both constraints active). -/
noncomputable def U (m : MechanicalGlut) (q : ℝ) : ℝ :=
  (m.k1 / 2) * (q - m.a)^2 + (m.k2 / 2) * (q - m.b)^2

/-- Derivative of the held potential, expressed algebraically. -/
def gradU (m : MechanicalGlut) (q : ℝ) : ℝ :=
  m.k1 * (q - m.a) + m.k2 * (q - m.b)

/-- Weighted force-balance position. -/
noncomputable def qStar (m : MechanicalGlut) : ℝ :=
  (m.k1 * m.a + m.k2 * m.b) / (m.k1 + m.k2)

/-- Conflict energy remaining at the minimum of the held energy. -/
noncomputable def epsilon (m : MechanicalGlut) : ℝ :=
  (m.k1 * m.k2 / (2 * (m.k1 + m.k2))) * (m.a - m.b)^2

private theorem ksum_pos (m : MechanicalGlut) : 0 < m.k1 + m.k2 :=
  add_pos m.k1_pos m.k2_pos

private theorem ksum_ne (m : MechanicalGlut) : m.k1 + m.k2 ≠ 0 :=
  ne_of_gt (ksum_pos m)

/-- Exactly zero net gradient at the held equilibrium. -/
theorem gradU_qStar (m : MechanicalGlut) : m.gradU m.qStar = 0 := by
  unfold gradU qStar
  field_simp [ksum_ne m]
  ring

/-- Completion of the square: exact analytical expression for all q. -/
theorem U_decomposition (m : MechanicalGlut) (q : ℝ) :
    m.U q = ((m.k1 + m.k2) / 2) * (q - m.qStar)^2 + m.epsilon := by
  unfold U qStar epsilon
  field_simp [ksum_ne m]
  ring

/-- The residual energy is strictly positive when the preferences differ. -/
theorem epsilon_pos (m : MechanicalGlut) : 0 < m.epsilon := by
  have hsq : 0 < (m.a - m.b)^2 := by
    have hne : m.a - m.b ≠ 0 := sub_ne_zero.mpr m.mismatch
    exact sq_pos_of_ne_zero hne
  unfold epsilon
  apply mul_pos
  · exact div_pos (mul_pos m.k1_pos m.k2_pos)
      (mul_pos (by norm_num : (0 : ℝ) < 2) (ksum_pos m))
  · exact hsq

/-- The equilibrium potential equals exactly the positive conflict residue. -/
theorem U_qStar (m : MechanicalGlut) : m.U m.qStar = m.epsilon := by
  rw [U_decomposition]
  ring

/-- qStar globally minimizes the held potential. -/
theorem U_qStar_le (m : MechanicalGlut) (q : ℝ) :
    m.U m.qStar ≤ m.U q := by
  rw [U_qStar, U_decomposition]
  have hfac : 0 ≤ (m.k1 + m.k2) / 2 :=
    le_of_lt (div_pos (ksum_pos m) (by norm_num))
  have hterm : 0 ≤ (m.k1 + m.k2) / 2 * (q - m.qStar)^2 :=
    mul_nonneg hfac (sq_nonneg _)
  linarith

/-- An exact, nonzero displacement from the first preferred configuration. -/
theorem qStar_sub_a (m : MechanicalGlut) :
    m.qStar - m.a = (m.k2 / (m.k1 + m.k2)) * (m.b - m.a) := by
  unfold qStar
  field_simp [ksum_ne m]
  ring

theorem qStar_ne_a (m : MechanicalGlut) : m.qStar ≠ m.a := by
  intro h
  have hdiff : m.b - m.a ≠ 0 := sub_ne_zero.mpr (Ne.symm m.mismatch)
  have hfactor : m.k2 / (m.k1 + m.k2) ≠ 0 :=
    div_ne_zero (ne_of_gt m.k2_pos) (ksum_ne m)
  have hnonzero : m.qStar - m.a ≠ 0 := by
    rw [qStar_sub_a]
    exact mul_ne_zero hfactor hdiff
  exact hnonzero (sub_eq_zero.mpr h)

/-- Potential after releasing the *second* constraint. -/
noncomputable def releasedU (m : MechanicalGlut) (q : ℝ) : ℝ :=
  (m.k1 / 2) * (q - m.a)^2

/-- Minimum of releasedU is zero, at a. -/
theorem releasedU_at_a (m : MechanicalGlut) : m.releasedU m.a = 0 := by
  simp [releasedU]

theorem releasedU_nonneg (m : MechanicalGlut) (q : ℝ) :
    0 ≤ m.releasedU q := by
  unfold releasedU
  exact mul_nonneg (le_of_lt (div_pos m.k1_pos (by norm_num)))
    (sq_nonneg _)

/-- E_g = U_g(q_held) - min U_g, since min U_g = U_g(a) = 0. -/
noncomputable def Eg (m : MechanicalGlut) : ℝ :=
  m.releasedU m.qStar - m.releasedU m.a

/-- Releasing the second preference leaves positive accessible potential. -/
theorem Eg_pos (m : MechanicalGlut) : 0 < m.Eg := by
  rw [Eg, releasedU_at_a]
  simp only [sub_zero, releasedU]
  apply mul_pos (div_pos m.k1_pos (by norm_num))
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr m.qStar_ne_a)

/-- The accessible energy of this release is no more than total held energy. -/
theorem Eg_le_epsilon (m : MechanicalGlut) : m.Eg ≤ m.epsilon := by
  rw [← U_qStar]
  simp only [Eg, releasedU_at_a, sub_zero, releasedU, U]
  have hnonneg : 0 ≤ m.k2 / 2 * (m.qStar - m.b)^2 :=
    mul_nonneg
      (le_of_lt (div_pos m.k2_pos (by norm_num))) (sq_nonneg _)
  linarith

/-- Output model: positive, at most unit efficiency for the released energy. -/
structure ProductiveRelease (m : MechanicalGlut) (Allowed : MechanicalGlut → Prop) where
  admissible : Allowed m
  eta : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1

/-- Extracted work (an explicit coupling assumption, not a free consequence). -/
noncomputable def Wext (m : MechanicalGlut) {Allowed : MechanicalGlut → Prop}
    (r : ProductiveRelease m Allowed) : ℝ :=
  r.eta * m.Eg

/-- Conditional work-conversion theorem with conservative bounds. -/
theorem productive_work (m : MechanicalGlut) {Allowed : MechanicalGlut → Prop}
    (r : ProductiveRelease m Allowed) :
    0 < m.Wext r ∧ m.Wext r ≤ m.Eg ∧ m.Wext r ≤ m.epsilon := by
  have hp : 0 < m.Wext r := mul_pos r.eta_pos m.Eg_pos
  have hle : m.Wext r ≤ m.Eg := by
    have h := mul_le_mul_of_nonneg_right r.eta_le_one
      (le_of_lt m.Eg_pos)
    simpa [Wext] using h
  exact ⟨hp, hle, le_trans hle m.Eg_le_epsilon⟩

end MechanicalGlut

/-! ## Faithful bridge from native SIXTEEN_3 information to mechanical mismatch -/

/-- A typed representation of a particular SIXTEEN_3 state in a mechanical
    plant. `faithfulBoth` is the substantive bridge condition: where positive and negative support coexist, the two mechanically represented preferences really differ.
    Positive stiffnesses and this reflection hypothesis are *input evidence*,
    not consequences of logic alone. -/
structure MechanicalEncoding (s : Sixteen3) where
  k1 : ℝ
  k2 : ℝ
  a : ℝ
  b : ℝ
  k1_pos : 0 < k1
  k2_pos : 0 < k2
  faithfulBoth : IsBoth s → a ≠ b

/-- Interpret Both-supported evidence as a concrete mechanical glut. -/
def MechanicalEncoding.realize {s : Sixteen3}
    (e : MechanicalEncoding s) (hB : IsBoth s) : MechanicalGlut :=
  { k1 := e.k1, k2 := e.k2, a := e.a, b := e.b,
    k1_pos := e.k1_pos, k2_pos := e.k2_pos, mismatch := e.faithfulBoth hB }

/-- The desired bridge, stated *conditionally* and proved algebraically. -/
theorem B_realizes_positive_energy (s : Sixteen3)
    (e : MechanicalEncoding s) (hB : IsBoth s) :
    0 < (e.realize hB).epsilon :=
  (e.realize hB).epsilon_pos

/-- A productive B-realization yields positive work, bounded by accessible
    release energy and by the original held residual energy. -/
theorem B_realizes_positive_bounded_work (s : Sixteen3)
    (e : MechanicalEncoding s) (hB : IsBoth s)
    {Allowed : MechanicalGlut → Prop}
    (r : MechanicalGlut.ProductiveRelease (e.realize hB) Allowed) :
    0 < (e.realize hB).Wext r ∧
    (e.realize hB).Wext r ≤ (e.realize hB).Eg ∧
    (e.realize hB).Wext r ≤ (e.realize hB).epsilon :=
  (e.realize hB).productive_work r

/-- Fourfold winding ensures a Both-supporting input for any *faithful encoding
    of the resulting state*; it does not manufacture a physical encoding. -/
theorem after_winding_realizes_positive_energy (s : Sixteen3)
    (e : MechanicalEncoding (wind (wind (wind (wind s))))) :
    0 < (e.realize (winding_four_isBoth s)).epsilon :=
  (e.realize (winding_four_isBoth s)).epsilon_pos

/-- Complete conditional logical-to-mechanical-to-output implication.
    Every native input reaches Both after four steps. If the resulting state
    has a faithful mechanical encoding and an admissible productive release,
    the output is strictly positive and energy bounded. -/
theorem after_winding_produces_bounded_work (s : Sixteen3)
    (e : MechanicalEncoding (wind (wind (wind (wind s)))))
    {Allowed : MechanicalGlut → Prop}
    (r : MechanicalGlut.ProductiveRelease
      (e.realize (winding_four_isBoth s)) Allowed) :
    0 < (e.realize (winding_four_isBoth s)).Wext r ∧
    (e.realize (winding_four_isBoth s)).Wext r ≤
      (e.realize (winding_four_isBoth s)).Eg ∧
    (e.realize (winding_four_isBoth s)).Wext r ≤
      (e.realize (winding_four_isBoth s)).epsilon :=
  (e.realize (winding_four_isBoth s)).productive_work r

/-! ## Lattice-resolved interaction laws

An interaction carries a response for each FOUR member before any projection
to aggregate support. The response is an explicit constitutive input. The
following composition laws follow from the native SIXTEEN_3 operations for
every such input, including negative force components. -/

namespace LatticeInteraction

/-- Read one membership without projecting the register to aggregate FOUR. -/
def member (s : Sixteen3) : Belnap → Bool
  | .N => s.hasN | .T => s.hasT | .F => s.hasF | .B => s.hasB

/-- Remove exactly one named membership, retaining the other three. -/
def remove (v : Belnap) (s : Sixteen3) : Sixteen3 :=
  match v with
  | .N => { s with hasN := false }
  | .T => { s with hasT := false }
  | .F => { s with hasF := false }
  | .B => { s with hasB := false }

/-- One native membership difference. Its repeated application extracts all
orders of interaction, including cooperative joint-membership responses. -/
noncomputable def difference (v : Belnap) (f : Sixteen3 → ℝ) (s : Sixteen3) : ℝ :=
  if member s v then f s - f (remove v s) else f s

/-- One inverse membership accumulation. -/
noncomputable def accumulate (v : Belnap) (f : Sixteen3 → ℝ) (s : Sixteen3) : ℝ :=
  if member s v then f s + f (remove v s) else f s

theorem accumulate_difference (v : Belnap) (f : Sixteen3 → ℝ) :
    accumulate v (difference v f) = f := by
  funext s
  cases v <;> simp [accumulate, difference, member, remove] <;>
    split <;> simp_all

theorem difference_accumulate (v : Belnap) (f : Sixteen3 → ℝ) :
    difference v (accumulate v f) = f := by
  funext s
  cases v <;> simp [accumulate, difference, member, remove] <;>
    split <;> simp_all

/-- Exact interaction coefficients of an arbitrary sixteen-state response.
This retains constant, singleton, pair, triple and four-member terms. -/
noncomputable def interactions (f : Sixteen3 → ℝ) : Sixteen3 → ℝ :=
  difference .B (difference .F (difference .T (difference .N f)))

/-- Recover the response from its full interaction coefficients. -/
noncomputable def reconstruct (f : Sixteen3 → ℝ) : Sixteen3 → ℝ :=
  accumulate .N (accumulate .T (accumulate .F (accumulate .B f)))

/-- Every native response has an exact joint-interaction decomposition. -/
theorem reconstruct_interactions (f : Sixteen3 → ℝ) :
    reconstruct (interactions f) = f := by
  simp only [reconstruct, interactions, accumulate_difference]

/-- The decomposition is unique: no distinct interaction family is hidden. -/
theorem interactions_reconstruct (f : Sixteen3 → ℝ) :
    interactions (reconstruct f) = f := by
  simp only [reconstruct, interactions, difference_accumulate]

/-- A joint-membership coefficient carries the corresponding difference
of physical derivatives, so cooperative forces keep their source states. -/
theorem difference_derivative (v : Belnap) (p g : Sixteen3 → ℝ → ℝ)
    (h : ∀ s q, HasDerivAt (p s) (g s q) q) (s : Sixteen3) (q : ℝ) :
    HasDerivAt (fun x => difference v (fun t => p t x) s)
      (difference v (fun t => g t q) s) q := by
  unfold difference
  split
  · exact (h s q).sub (h (remove v s) q)
  · exact h s q

/-- A cooperative T/F term is retained at their joint support, even when
each separate singleton has zero response. -/
theorem cooperative_pair_coefficient (k : ℝ) (s : Sixteen3) :
    interactions (fun x => if x.hasT && x.hasF then k else 0) s =
      if s = separatedBoth then k else 0 := by
  rcases s with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;>
    simp [interactions, difference, member, remove, separatedBoth, Sixteen3.ofBelnap]

/-- Evaluate the responses of precisely the members held in the register.
No division by the number of members or projection to aggregate B occurs. -/
noncomputable def response (s : Sixteen3) (r : Belnap → ℝ) : ℝ :=
  (if s.hasN then r .N else 0) + (if s.hasT then r .T else 0) +
  (if s.hasF then r .F else 0) + (if s.hasB then r .B else 0)

private theorem member_union_intersection (a b : Bool) (v : ℝ) :
    (if a || b then v else 0) + (if a && b then v else 0) =
      (if a then v else 0) + (if b then v else 0) := by
  cases a <;> cases b <;> simp

/-- Exact gluing law, retaining and accounting for shared interaction support.
It applies independently to energy and to every force component. -/
theorem fuse_response (s t : Sixteen3) (r : Belnap → ℝ) :
    response (Sixteen3.join_i s t) r + response (Sixteen3.meet_i s t) r =
      response s r + response t r := by
  unfold response Sixteen3.join_i Sixteen3.meet_i
  have hN := member_union_intersection s.hasN t.hasN (r .N)
  have hT := member_union_intersection s.hasT t.hasT (r .T)
  have hF := member_union_intersection s.hasF t.hasF (r .F)
  have hB := member_union_intersection s.hasB t.hasB (r .B)
  linarith

/-- Applying the information fuse twice to the same support adds no energy. -/
theorem fuse_idempotent (s : Sixteen3) (r : Belnap → ℝ) :
    response (Sixteen3.join_i s s) r = response s r := by
  simp [response, Sixteen3.join_i]

/-- The truth-order split redistributes support with the same exact balance. -/
theorem truth_response_balance (s t : Sixteen3) (r : Belnap → ℝ) :
    response (Sixteen3.join_t s t) r + response (Sixteen3.meet_t s t) r =
      response s r + response t r := by
  unfold response Sixteen3.join_t Sixteen3.meet_t
  have hN := member_union_intersection s.hasN t.hasN (r .N)
  have hT := member_union_intersection s.hasT t.hasT (r .T)
  have hF := member_union_intersection s.hasF t.hasF (r .F)
  have hB := member_union_intersection s.hasB t.hasB (r .B)
  linarith

/-- The kernel's independent falsity-order split also balances responses. -/
theorem falsity_response_balance (s t : Sixteen3) (r : Belnap → ℝ) :
    response (Sixteen3.join_f s t) r + response (Sixteen3.meet_f s t) r =
      response s r + response t r := by
  unfold response Sixteen3.join_f Sixteen3.meet_f
  have hN := member_union_intersection s.hasN t.hasN (r .N)
  have hT := member_union_intersection s.hasT t.hasT (r .T)
  have hF := member_union_intersection s.hasF t.hasF (r .F)
  have hB := member_union_intersection s.hasB t.hasB (r .B)
  linarith

/-- The sum of disjoint branches equals the response after their fuse. -/
theorem disjoint_split_fuse (s t : Sixteen3) (r : Belnap → ℝ)
    (h : Sixteen3.meet_i s t = unmarked) :
    response (Sixteen3.join_i s t) r = response s r + response t r := by
  have hf := fuse_response s t r
  rw [h] at hf
  simpa [response, unmarked, Sixteen3.ofBelnap] using hf

theorem response_nonnegative (s : Sixteen3) (r : Belnap → ℝ)
    (h : ∀ v, 0 ≤ r v) : 0 ≤ response s r := by
  unfold response
  have member (b : Bool) (v : Belnap) : 0 ≤ (if b then r v else 0) := by
    split <;> simp_all
  exact add_nonneg (add_nonneg (add_nonneg (member s.hasN .N)
    (member s.hasT .T)) (member s.hasF .F)) (member s.hasB .B)

/-- Each branch keeps its own mechanical law and its checked derivative. -/
structure PotentialFamily where
  potential : Belnap → ℝ → ℝ
  slope : Belnap → ℝ → ℝ
  derivative : ∀ v q, HasDerivAt (potential v) (slope v q) q

noncomputable def PotentialFamily.energy (p : PotentialFamily)
    (s : Sixteen3) (q : ℝ) : ℝ := response s (fun v => p.potential v q)

noncomputable def PotentialFamily.force (p : PotentialFamily)
    (s : Sixteen3) (q : ℝ) : ℝ := -response s (fun v => p.slope v q)

/-- Differentiation commutes with the exact membership-resolved response. -/
theorem PotentialFamily.energy_derivative (p : PotentialFamily)
    (s : Sixteen3) (q : ℝ) :
    HasDerivAt (p.energy s) (-p.force s q) q := by
  have member (b : Bool) (v : Belnap) :
      HasDerivAt (fun x => if b then p.potential v x else 0)
        (if b then p.slope v q else 0) q := by
    cases b
    · simpa using hasDerivAt_const q (0 : ℝ)
    · simpa using p.derivative v q
  simpa [PotentialFamily.energy, PotentialFamily.force, response] using
    (((member s.hasN .N).add (member s.hasT .T)).add
      (member s.hasF .F)).add (member s.hasB .B)

/-- Forces glue with the same shared-support correction as potentials. -/
theorem PotentialFamily.force_fuse (p : PotentialFamily)
    (s t : Sixteen3) (q : ℝ) :
    p.force (Sixteen3.join_i s t) q + p.force (Sixteen3.meet_i s t) q =
      p.force s q + p.force t q := by
  unfold PotentialFamily.force
  linarith [fuse_response s t (fun v => p.slope v q)]

/-- A pair potential on relative displacement is invariant under common motion. -/
theorem PotentialFamily.common_translation (p : PotentialFamily)
    (s : Sixteen3) (x y c : ℝ) :
    p.energy s ((x+c)-(y+c)) = p.energy s (x-y) := by
  congr 1
  ring

/-- Left and right mechanical forces for a relative-displacement interaction. -/
theorem PotentialFamily.pair_forces (p : PotentialFamily)
    (s : Sixteen3) (x y : ℝ) :
    HasDerivAt (fun z => p.energy s (z-y)) (-p.force s (x-y)) x ∧
    HasDerivAt (fun z => p.energy s (x-z)) (p.force s (x-y)) y := by
  constructor
  · simpa using (p.energy_derivative s (x-y)).comp x ((hasDerivAt_id x).sub_const y)
  · simpa using (p.energy_derivative s (x-y)).comp y ((hasDerivAt_id y).const_sub x)

/-- The two physical branch responses remain observable after aggregate
support identifies both registers with FOUR.B. -/
theorem separated_and_singleton_responses (r : Belnap → ℝ) :
    response separatedBoth r = r .T + r .F ∧ response onlyB r = r .B := by
  simp [response, separatedBoth, onlyB, Sixteen3.ofBelnap]

/-- The mechanical gradient is the analytic derivative of the held potential. -/
theorem mechanical_derivative (m : MechanicalGlut) (q : ℝ) :
    HasDerivAt m.U (m.gradU q) q := by
  convert ((((hasDerivAt_id q).sub_const m.a).pow 2).const_mul (m.k1/2)).add
    ((((hasDerivAt_id q).sub_const m.b).pow 2).const_mul (m.k2/2)) using 1 <;>
    dsimp [MechanicalGlut.U, MechanicalGlut.gradU] <;> ring

/-- Exact energy accounting for a gradient-directed conformational step. -/
theorem mechanical_step_work (m : MechanicalGlut) (q eta : ℝ) :
    m.U q - m.U (q-eta*m.gradU q) =
      eta * (1-eta*(m.k1+m.k2)/2) * (m.gradU q)^2 := by
  unfold MechanicalGlut.U MechanicalGlut.gradU
  ring

/-- Positive stiffness supplies an explicit step interval for strict descent. -/
theorem mechanical_step_lowers_energy (m : MechanicalGlut) (q eta : ℝ)
    (heta : 0 < eta) (hbound : eta < 2/(m.k1+m.k2))
    (hmoving : m.gradU q ≠ 0) : m.U (q-eta*m.gradU q) < m.U q := by
  have hsum : 0 < m.k1+m.k2 := add_pos m.k1_pos m.k2_pos
  have hproduct : eta*(m.k1+m.k2) < 2 := (lt_div_iff₀ hsum).mp hbound
  have hremaining : 0 < 1-eta*(m.k1+m.k2)/2 := by linarith
  have hdrop : 0 < m.U q - m.U (q-eta*m.gradU q) := by
    rw [mechanical_step_work]
    exact mul_pos (mul_pos heta hremaining) (sq_pos_of_ne_zero hmoving)
  exact sub_pos.mp hdrop

end LatticeInteraction

/-! ## Native-unit Glut parameters from the retained memberships

The Hasse-edge unit is one membership. Positive and negative stiffnesses
count their independently retained supports. The preferred separation is
the extent of those two source-addressed support frames. This specifies a
native-unit realization without supplying real-valued plant parameters. -/
namespace NativeGlut

def positive (s : Sixteen3) : ℕ := s.hasT.toNat + s.hasB.toNat
def negative (s : Sixteen3) : ℕ := s.hasF.toNat + s.hasB.toNat

theorem positive_of_both (s : Sixteen3) (h : IsBoth s) : 0 < positive s := by
  rcases s with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;>
    simp_all [IsBoth, supportPlus, supportMinus, positive]

theorem negative_of_both (s : Sixteen3) (h : IsBoth s) : 0 < negative s := by
  rcases s with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;>
    simp_all [IsBoth, supportPlus, supportMinus, negative]

/-- All mechanical inputs are computed from the native support frames.
Zero is the coincident boundary; the other preference is their combined
Hasse extent. The source register and its Both evidence remain parameters. -/
noncomputable def encoding (s : Sixteen3) (h : IsBoth s) : MechanicalEncoding s where
  k1 := positive s
  k2 := negative s
  a := 0
  b := (positive s : ℝ) + negative s
  k1_pos := by exact_mod_cast positive_of_both s h
  k2_pos := by exact_mod_cast negative_of_both s h
  faithfulBoth := by
    intro _
    have hp : (0 : ℝ) < positive s := by exact_mod_cast positive_of_both s h
    have hn : (0 : ℝ) < negative s := by exact_mod_cast negative_of_both s h
    exact ne_of_lt (add_pos hp hn)

/-- Native equilibrium separation equals the negative-frame extent. -/
theorem equilibrium (s : Sixteen3) (h : IsBoth s) :
    ((encoding s h).realize h).qStar = negative s := by
  have hp : (0 : ℝ) < positive s := by exact_mod_cast positive_of_both s h
  have hn : (0 : ℝ) < negative s := by exact_mod_cast negative_of_both s h
  have hsum : (positive s : ℝ) + negative s ≠ 0 := ne_of_gt (add_pos hp hn)
  dsimp [MechanicalGlut.qStar, MechanicalEncoding.realize, encoding]
  field_simp
  <;> ring

/-- The retained strain is a cooperative polynomial in the two native extents. -/
theorem retained_strain (s : Sixteen3) (h : IsBoth s) :
    ((encoding s h).realize h).epsilon =
      (positive s : ℝ) * negative s * (positive s + negative s) / 2 := by
  have hp : (0 : ℝ) < positive s := by exact_mod_cast positive_of_both s h
  have hn : (0 : ℝ) < negative s := by exact_mod_cast negative_of_both s h
  have hsum : (positive s : ℝ) + negative s ≠ 0 := ne_of_gt (add_pos hp hn)
  dsimp [MechanicalGlut.epsilon, MechanicalEncoding.realize, encoding]
  field_simp
  <;> ring

/-- The original specified release now has no supplied stiffness or distance. -/
theorem released_work (s : Sixteen3) (h : IsBoth s) :
    ((encoding s h).realize h).Eg = (positive s : ℝ) * (negative s : ℝ)^2 / 2 := by
  unfold MechanicalGlut.Eg
  rw [equilibrium]
  dsimp [MechanicalGlut.releasedU, MechanicalEncoding.realize, encoding]
  ring

end NativeGlut

namespace NativeFrame

/-- The three nontrivial characters of the native FOUR evidence pair. -/
def truthCharacter (v : Belnap) : ℚ := if designated v then -1 else 1
def falseCharacter (v : Belnap) : ℚ := if designated (bnot v) then -1 else 1
def vertex (v : Belnap) : ℚ × ℚ × ℚ :=
  (truthCharacter v, falseCharacter v, truthCharacter v * falseCharacter v)
def dot (x y : ℚ × ℚ × ℚ) : ℚ := x.1*y.1 + x.2.1*y.2.1 + x.2.2*y.2.2

/-- FOUR's character geometry has the regular tetrahedral Gram matrix. -/
theorem vertex_gram (v w : Belnap) :
    dot (vertex v) (vertex w) = if v=w then 3 else -1 := by
  cases v <;> cases w <;>
    norm_num [dot, vertex, truthCharacter, falseCharacter, designated, bnot] <;> decide

/-- The tetrahedral angle ratio is computed by the native characters. -/
theorem tetrahedral_ratio (v w : Belnap) (h : v ≠ w) :
    dot (vertex v) (vertex w) / dot (vertex v) (vertex v) = -(1/3 : ℚ) := by
  norm_num [vertex_gram, h]

/-- Centre the three-member face opposite the native N vertex. -/
def faceVertex (v : Belnap) : ℚ × ℚ × ℚ :=
  ((vertex v).1 + (vertex .N).1/3,
   (vertex v).2.1 + (vertex .N).2.1/3,
   (vertex v).2.2 + (vertex .N).2.2/3)

theorem face_gram (v w : Belnap) (hv : v ≠ .N) (hw : w ≠ .N) :
    dot (faceVertex v) (faceVertex w) = if v=w then 8/3 else -4/3 := by
  cases v <;> cases w <;>
    norm_num [dot, faceVertex, vertex, truthCharacter, falseCharacter,
      designated, bnot] at * <;> decide

/-- Three-member support has the planar angle ratio, without an angle table. -/
theorem planar_ratio (v w : Belnap) (hv : v ≠ .N) (hw : w ≠ .N) (h : v ≠ w) :
    dot (faceVertex v) (faceVertex w) / dot (faceVertex v) (faceVertex v) = -(1/2 : ℚ) := by
  norm_num [face_gram, hv, hw, h]

end NativeFrame

namespace NativeSelection

/-- The three orders offer six views of one source-addressed interaction. -/
def contexts (s t : Sixteen3) : List Sixteen3 :=
  [Sixteen3.join_i s t, Sixteen3.meet_i s t,
   Sixteen3.join_t s t, Sixteen3.meet_t s t,
   Sixteen3.join_f s t, Sixteen3.meet_f s t]

/-- The information join dominates every offered context in inclusion order.
This comparison retains all four memberships and uses no mechanical score. -/
theorem contexts_bounded (s t : Sixteen3) :
    ((contexts s t).all fun z => Sixteen3.le_i z (Sixteen3.join_i s t)) = true := by
  rcases s with ⟨sn,st,sf,sb⟩
  rcases t with ⟨tn,tt,tf,tb⟩
  cases sn <;> cases st <;> cases sf <;> cases sb <;>
    cases tn <;> cases tt <;> cases tf <;> cases tb <;> decide

/-- The maximum is reachable: it is an offered context, not an injected top. -/
theorem maximum_offered (s t : Sixteen3) :
    Sixteen3.join_i s t ∈ contexts s t := by
  simp [contexts]

/-- Retention of offered evidence is inflationary in the information order. -/
theorem retain_information (s t : Sixteen3) :
    Sixteen3.le_i s (Sixteen3.join_i s t) = true := by
  rcases s with ⟨sn,st,sf,sb⟩
  rcases t with ⟨tn,tt,tf,tb⟩
  cases sn <;> cases st <;> cases sf <;> cases sb <;>
    cases tn <;> cases tt <;> cases tf <;> cases tb <;> decide

/-- An already retained source observation is idempotent under re-entry. -/
theorem retain_idempotent (s : Sixteen3) : Sixteen3.join_i s s = s := by
  rcases s with ⟨n,t,f,b⟩
  simp [Sixteen3.join_i]

end NativeSelection

end Imscribing.PrimaLogica.MechanicalGlut
