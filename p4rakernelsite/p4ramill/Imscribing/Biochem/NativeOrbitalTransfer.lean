import Imscribing.Biochem.PrimaLogicaMechanicalGlut
import Imscribing.Paraconsistent.OrbitalBelnap

/-! Two-site orbital rewriting on the retained powerset carrier. The two
spin occupancies come from OrbitalBelnap's FOUR. Rewriting retains every
placement with the same two spin counts. No element identities, chemical
valences or dimensional parameters are supplied. -/
namespace Imscribing.PrimaLogica.NativeOrbitalTransfer
open Lean Imscribing.Paraconsistent Imscribing.Paraconsistent.Orbital

instance : Fintype OrbitalState where
  elems := {.empty, .spinUp, .spinDown, .paired}
  complete := by intro x; cases x <;> simp

def up : OrbitalState → Nat
  | .empty | .spinDown => 0
  | .spinUp | .paired => 1
def down : OrbitalState → Nat
  | .empty | .spinUp => 0
  | .spinDown | .paired => 1
def occupied (x : OrbitalState) := up x + down x
def vacant (x : OrbitalState) := (1 - up x) + (1 - down x)

theorem slot_accounting (x : OrbitalState) : occupied x + vacant x = 2 := by
  cases x <;> decide
theorem capacity (x : OrbitalState) : occupied x ≤ 2 := by
  cases x <;> decide

/-- Creation uses the native pair operation only when its spin slot is free.
An occupied slot has no successor, rather than an idempotent fake addition. -/
def create (x : OrbitalState) (spinUp : Bool) : Option OrbitalState :=
  if (if spinUp then up x else down x) = 0 then
    some (pair x (if spinUp then .spinUp else .spinDown))
  else none

theorem create_adds_one (x y : OrbitalState) (s : Bool)
    (h : create x s = some y) : occupied y = occupied x + 1 := by
  cases x <;> cases s <;>
    simp [create, up, down, pair] at h <;> subst y <;> decide

theorem create_preserves_information (x y : OrbitalState) (s : Bool)
    (h : create x s = some y) : OccupancyLE x y := by
  cases x <;> cases s <;>
    simp [create, up, down, pair] at h <;> subst y <;> decide

theorem create_paired_blocked (s : Bool) : create .paired s = none := by
  cases s <;> rfl

theorem create_opposite_fuses (s : Bool) :
    create (if s then .spinUp else .spinDown) (!s) = some .paired := by
  cases s <;> rfl

theorem create_recovers_split_pair :
    create (depair .paired).1 false = some .paired ∧
    create (depair .paired).2 true = some .paired := by
  constructor <;> rfl

/-! An indexed shell retains the shared orbital placements. Unpaired capacity
is an occupancy readout; it does not assign elemental names to shell inputs. -/
def single : OrbitalState → Nat
  | .spinUp | .spinDown => 1
  | .empty | .paired => 0
def pairedCount : OrbitalState → Nat
  | .paired => 1
  | _ => 0
def emptyCount : OrbitalState → Nat
  | .empty => 1
  | _ => 0

theorem occupied_single_pair (x : OrbitalState) :
    single x + 2 * pairedCount x = occupied x := by
  cases x <;> decide
theorem vacant_single_empty (x : OrbitalState) :
    single x + 2 * emptyCount x = vacant x := by
  cases x <;> decide

def shellOccupied (s : List OrbitalState) : Nat := (s.map occupied).sum
def shellVacant (s : List OrbitalState) : Nat := (s.map vacant).sum
def shellSingle (s : List OrbitalState) : Nat := (s.map single).sum
def shellPaired (s : List OrbitalState) : Nat := (s.map pairedCount).sum
def shellEmpty (s : List OrbitalState) : Nat := (s.map emptyCount).sum

theorem shell_slot_accounting (s : List OrbitalState) :
    shellOccupied s + shellVacant s = 2 * s.length := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    simp only [shellOccupied, shellVacant, List.map_cons, List.sum_cons,
      List.length_cons] at *
    have hx := slot_accounting x
    omega

theorem shell_occupied_accounting (s : List OrbitalState) :
    shellSingle s + 2 * shellPaired s = shellOccupied s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    simp only [shellSingle, shellPaired, shellOccupied, List.map_cons,
      List.sum_cons] at *
    have hx := occupied_single_pair x
    omega

theorem shell_vacant_accounting (s : List OrbitalState) :
    shellSingle s + 2 * shellEmpty s = shellVacant s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    simp only [shellSingle, shellEmpty, shellVacant, List.map_cons,
      List.sum_cons] at *
    have hx := vacant_single_empty x
    omega

/-- Unpaired bonding capacity is bounded by both occupied and vacant slots.
The full correlated family remains retained on either side of this readout. -/
theorem shell_single_capacity_bound (s : List OrbitalState) :
    shellSingle s ≤ min (shellOccupied s) (shellVacant s) := by
  have ho := shell_occupied_accounting s
  have hv := shell_vacant_accounting s
  omega

/-! Native mechanical readouts on the full filling family. Information-order
selection retains that entire family. This minimum is an energy observation
for the explicitly summed existing Glut coupling, not a state deletion. -/
def spinGlutDouble (p n : Nat) : Nat := p*n*(p+n)
def shellGlutDouble : List OrbitalState → Nat
  | [] => 0
  | x::xs => spinGlutDouble (up x) (down x) + shellGlutDouble xs +
      (xs.map fun y => spinGlutDouble (up x+up y) (down x+down y)).sum

def fillingStates : Nat → List (List OrbitalState)
  | 0 => [[]]
  | n+1 => (fillingStates n).flatMap fun xs =>
      ([.empty,.spinUp,.spinDown,.paired] : List OrbitalState).map fun x => x::xs

theorem mem_fillingStates (s : List OrbitalState) : s ∈ fillingStates s.length := by
  induction s with
  | nil => simp [fillingStates]
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨xs, ih, ?_⟩
    apply List.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    cases x <;> simp

def minimumGlutDouble (k electrons : Nat) : Nat :=
  2*(electrons-k)*(2*k+electrons-3)
def polarized (s : List OrbitalState) : Bool :=
  let u := (s.map up).sum
  let d := (s.map down).sum
  u == 0 || d == 0 || u == s.length || d == s.length

set_option maxRecDepth 100000 in
private theorem filling_readout_certificate :
    ((List.range 5).all fun k => (fillingStates k).all fun s =>
      decide (minimumGlutDouble k (shellOccupied s) ≤ shellGlutDouble s) &&
      (if shellGlutDouble s == minimumGlutDouble k (shellOccupied s) then
        decide (shellSingle s = min (shellOccupied s) (2*k-shellOccupied s)) && polarized s
       else true)) = true := by decide

theorem filling_glut_lower_bound (s : List OrbitalState) (hk : s.length ≤ 4) :
    minimumGlutDouble s.length (shellOccupied s) ≤ shellGlutDouble s := by
  have hc := (List.all_eq_true.mp filling_readout_certificate)
    s.length (List.mem_range.mpr (by omega))
  have hs := (List.all_eq_true.mp hc) s (mem_fillingStates s)
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

theorem minimum_filling_has_maximal_singles (s : List OrbitalState)
    (hk : s.length ≤ 4)
    (he : shellGlutDouble s = minimumGlutDouble s.length (shellOccupied s)) :
    shellSingle s = min (shellOccupied s) (2*s.length-shellOccupied s) ∧
      polarized s = true := by
  have hc := (List.all_eq_true.mp filling_readout_certificate)
    s.length (List.mem_range.mpr (by omega))
  have hs := (List.all_eq_true.mp hc) s (mem_fillingStates s)
  simp [he] at hs
  exact hs

/-- A constructive readout attaining the bound; the reversed spin family
is retained alongside it by fillingStates. -/
def filledReadout (k electrons : Nat) : List OrbitalState :=
  if electrons ≤ k then
    List.replicate electrons .spinUp ++ List.replicate (k-electrons) .empty
  else List.replicate (electrons-k) .paired ++ List.replicate (2*k-electrons) .spinUp

set_option maxRecDepth 100000 in
theorem filling_minimum_attained :
    ((List.range 5).all fun k => (List.range (2*k+1)).all fun e =>
      decide ((filledReadout k e).length = k ∧
        shellOccupied (filledReadout k e) = e ∧
        shellGlutDouble (filledReadout k e) = minimumGlutDouble k e)) = true := by decide

abbrev Joint := OrbitalState × OrbitalState
def allJoints : List Joint :=
  ([.empty,.spinUp,.spinDown,.paired] : List OrbitalState).flatMap fun a =>
    ([.empty,.spinUp,.spinDown,.paired] : List OrbitalState).map fun b => (a,b)
def sector (x : Joint) : Nat × Nat := (up x.1 + up x.2, down x.1 + down x.2)
def alternatives (x : Joint) : Finset Joint :=
  Finset.univ.filter fun y => sector y = sector x
def move (x : Joint) (swapUp swapDown : Bool) : Joint :=
  let a := depair x.1
  let b := depair x.2
  (pair (if swapUp then b.1 else a.1) (if swapDown then b.2 else a.2),
   pair (if swapUp then a.1 else b.1) (if swapDown then a.2 else b.2))
def nativeMoves (x : Joint) : Finset Joint :=
  {move x false false, move x false true, move x true false, move x true true}

/-- Split both orbitals, exchange either spin component, and fuse. These
four native operations generate exactly the conserved family. -/
theorem native_moves_complete (x : Joint) : nativeMoves x = alternatives x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

def close (K : Finset Joint) : Finset Joint := K.biUnion alternatives

@[simp] theorem mem_alternatives (x y : Joint) :
    y ∈ alternatives x ↔ sector y = sector x := by simp [alternatives]

theorem conservation (x y : Joint) (h : y ∈ alternatives x) :
    up y.1 + up y.2 = up x.1 + up x.2 ∧
    down y.1 + down y.2 = down x.1 + down x.2 := by
  have e := (mem_alternatives x y).mp h
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

theorem extensive (K : Finset Joint) : K ⊆ close K := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨x, hx, by simp⟩

theorem monotone {K L : Finset Joint} (h : K ⊆ L) : close K ⊆ close L := by
  intro y hy
  obtain ⟨x,hx,hyx⟩ := Finset.mem_biUnion.mp hy
  exact Finset.mem_biUnion.mpr ⟨x,h hx,hyx⟩

theorem idempotent (K : Finset Joint) : close (close K) = close K := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨z,hz,hyz⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x,hx,hzx⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨x,hx,
      (mem_alternatives x y).mpr (((mem_alternatives z y).mp hyz).trans
        ((mem_alternatives x z).mp hzx))⟩
  · exact extensive (close K)

/-- The retained family is the inclusion maximum of all admitted rewrites. -/
theorem maximum (K L : Finset Joint)
    (h : ∀ y ∈ L, ∃ x ∈ K, y ∈ alternatives x) : L ⊆ close K := by
  intro y hy
  obtain ⟨x,hx,hyx⟩ := h y hy
  exact Finset.mem_biUnion.mpr ⟨x,hx,hyx⟩

def contains (s : Sixteen3) : Belnap → Bool
  | .N => s.hasN | .T => s.hasT | .F => s.hasF | .B => s.hasB
def orbitalUp (s : Sixteen3) : Nat :=
  ([.empty,.spinUp,.spinDown,.paired] : List OrbitalState).foldl
    (fun n x => n + if contains s (orbToB4 x) then up x else 0) 0
def orbitalDown (s : Sixteen3) : Nat :=
  ([.empty,.spinUp,.spinDown,.paired] : List OrbitalState).foldl
    (fun n x => n + if contains s (orbToB4 x) then down x else 0) 0

theorem glut_positive_is_orbital_support (s : Sixteen3) :
    MechanicalGlut.NativeGlut.positive s = orbitalUp s := by
  rcases s with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide
theorem glut_negative_is_orbital_support (s : Sixteen3) :
    MechanicalGlut.NativeGlut.negative s = orbitalDown s := by
  rcases s with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> decide
def source (s t : Sixteen3) : Finset Joint :=
  Finset.univ.filter fun x => contains s (orbToB4 x.1) && contains t (orbToB4 x.2)
def family (s t : Sixteen3) : Finset Joint := close (source s t)
def marginal (K : Finset Joint) : Sixteen3 := Sixteen3.ofBelnap
  (allJoints.any fun x => decide (x ∈ K) && (orbToB4 x.1 == .N || orbToB4 x.2 == .N))
  (allJoints.any fun x => decide (x ∈ K) && (orbToB4 x.1 == .T || orbToB4 x.2 == .T))
  (allJoints.any fun x => decide (x ∈ K) && (orbToB4 x.1 == .F || orbToB4 x.2 == .F))
  (allJoints.any fun x => decide (x ∈ K) && (orbToB4 x.1 == .B || orbToB4 x.2 == .B))
def selected (s t : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i (Sixteen3.join_i s t) (marginal (family s t))

theorem opposed_spins_retained :
    alternatives (.spinUp,.spinDown) =
      {(.spinUp,.spinDown),(.spinDown,.spinUp),(.paired,.empty),(.empty,.paired)} := by
  decide
theorem double_pair_excluded :
    (.paired,.paired) ∉ alternatives (.spinUp,.spinDown) := by decide

/-- The same Glut polynomial acts at each carried spatial channel. Both
coefficients are the conserved source-addressed spin counts. -/
theorem spatial_glut_decomposition (p n q : ℝ) :
    (p*q^2+n*(q-(p+n))^2)/2 =
      (p+n)*(q-n)^2/2+p*n*(p+n)/2 := by ring
theorem spatial_glut_force (p n q : ℝ) :
    p*q+n*(q-(p+n)) = (p+n)*(q-n) := by ring
theorem transfer_preserves_spatial_coefficients (x y : Joint)
    (h : y ∈ alternatives x) :
    up y.1 + up y.2 = up x.1 + up x.2 ∧
    down y.1 + down y.2 = down x.1 + down x.2 := conservation x y h

/-- Splitting held energy into coordinate deformation and the banked Glut
release coordinate agrees with the original plant on its prepared slice. -/
noncomputable def releasedLift (p n q z : ℝ) : ℝ :=
  (p+n)*(q-n)^2/2+p*z^2/2+n*(n-(p+n))^2/2
theorem prepared_release_lift (p n q : ℝ) :
    releasedLift p n q n = (p*q^2+n*(q-(p+n))^2)/2 := by
  unfold releasedLift
  ring
theorem released_lift_exchange (p n qb qa zb za : ℝ)
    (h : (p+n)*(qa-n)^2/2-(p+n)*(qb-n)^2/2 = p*(zb^2-za^2)/2) :
    releasedLift p n qa za = releasedLift p n qb zb := by
  unfold releasedLift
  linear_combination h

abbrev Plant := MechanicalGlut.MechanicalGlut
abbrev Release (m : Plant) (Allowed : Plant → Prop) :=
  MechanicalGlut.MechanicalGlut.ProductiveRelease m Allowed

/-- Coupling efficiency is obtained from measured output work and checked
against the source release budget; it is not supplied as a fitted value. -/
noncomputable def measuredRelease (m : Plant) {Allowed : Plant → Prop}
    (admissible : Allowed m) (work : ℝ) (hw : 0 < work) (hle : work ≤ m.Eg) :
    Release m Allowed where
  admissible := admissible
  eta := work/m.Eg
  eta_pos := div_pos hw m.Eg_pos
  eta_le_one := (div_le_one m.Eg_pos).mpr hle

theorem measured_release_work (m : Plant) {Allowed : Plant → Prop}
    (admissible : Allowed m) (work : ℝ) (hw : 0 < work) (hle : work ≤ m.Eg) :
    m.Wext (measuredRelease m admissible work hw hle) = work := by
  simp only [MechanicalGlut.MechanicalGlut.Wext, measuredRelease]
  exact div_mul_cancel₀ work (ne_of_gt m.Eg_pos)

def jointIndex (x : Joint) : Nat :=
  4 * belnapToNat (orbToB4 x.1) + belnapToNat (orbToB4 x.2)
def jointMask (K : Finset Joint) : Nat :=
  allJoints.foldl (fun mask x => if x ∈ K then mask + 2 ^ jointIndex x else mask) 0
def nativeMask (s : Sixteen3) : Nat :=
  s.hasN.toNat + 2*s.hasT.toNat + 4*s.hasF.toNat + 8*s.hasB.toNat

#print axioms conservation
#print axioms create_adds_one
#print axioms create_preserves_information
#print axioms create_paired_blocked
#print axioms create_opposite_fuses
#print axioms create_recovers_split_pair
#print axioms shell_slot_accounting
#print axioms shell_occupied_accounting
#print axioms shell_vacant_accounting
#print axioms shell_single_capacity_bound
#print axioms filling_glut_lower_bound
#print axioms minimum_filling_has_maximal_singles
#print axioms filling_minimum_attained
#print axioms extensive
#print axioms monotone
#print axioms idempotent
#print axioms maximum
#print axioms native_moves_complete
#print axioms glut_positive_is_orbital_support
#print axioms glut_negative_is_orbital_support
#print axioms spatial_glut_decomposition
#print axioms spatial_glut_force
#print axioms prepared_release_lift
#print axioms released_lift_exchange
#print axioms measured_release_work
end Imscribing.PrimaLogica.NativeOrbitalTransfer
