import Mathlib

namespace Imscribing.Stage301_315

abbrev Vec (n : Nat) := Fin n → Nat

def Layer {n : Nat} (v : Vec n) (t : Nat) : Set (Fin n) :=
  {i | t ≤ v i}

def CarryCoeff {n : Nat} (v w : Vec n) (t : Nat) : Set (Fin n) :=
  {i | ∃ a b : Nat, a + b = t ∧ i ∈ Layer v a ∧ i ∈ Layer w b}

theorem layer_zero {n : Nat} (v : Vec n) :
    Layer v 0 = Set.univ := by
  ext i
  simp [Layer]

theorem layer_descends {n : Nat} (v : Vec n) {s t : Nat} (hst : s ≤ t) :
    Layer v t ⊆ Layer v s := by
  intro i hi
  simp [Layer] at hi ⊢
  omega

theorem layer_add_iff_carry {n : Nat} (v w : Vec n) (t : Nat) (i : Fin n) :
    i ∈ Layer (fun j => v j + w j) t ↔
      ∃ a b : Nat, a + b = t ∧ i ∈ Layer v a ∧ i ∈ Layer w b := by
  simp only [Layer, Set.mem_setOf_eq]
  constructor
  · intro hsum
    by_cases htv : t ≤ v i
    · refine ⟨t, 0, ?_, htv, ?_⟩
      · omega
      · omega
    · have hvlt : v i < t := Nat.lt_of_not_ge htv
      refine ⟨v i, t - v i, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
  · rintro ⟨a, b, hab, ha, hb⟩
    omega

theorem carryCoeff_eq_layer_add {n : Nat} (v w : Vec n) (t : Nat) :
    CarryCoeff v w t = Layer (fun i => v i + w i) t := by
  ext i
  simp only [CarryCoeff, Set.mem_setOf_eq]
  exact (layer_add_iff_carry v w t i).symm

theorem support_add {n : Nat} (v w : Vec n) :
    Layer (fun i => v i + w i) 1 = Layer v 1 ∪ Layer w 1 := by
  ext i
  simp [Layer]
  omega

theorem first_carry {n : Nat} (v w : Vec n) :
    Layer (fun i => v i + w i) 2 =
      Layer v 2 ∪ Layer w 2 ∪ (Layer v 1 ∩ Layer w 1) := by
  ext i
  simp [Layer]
  omega

theorem layer_add_comm {n : Nat} (v w : Vec n) (t : Nat) :
    Layer (fun i => v i + w i) t =
      Layer (fun i => w i + v i) t := by
  ext i
  simp [Layer, Nat.add_comm]

theorem layer_add_assoc {n : Nat} (u v w : Vec n) (t : Nat) :
    Layer (fun i => (u i + v i) + w i) t =
      Layer (fun i => u i + (v i + w i)) t := by
  ext i
  simp [Layer, Nat.add_assoc]

theorem layer_meet {n : Nat} (v w : Vec n) (t : Nat) :
    Layer (fun i => min (v i) (w i)) t = Layer v t ∩ Layer w t := by
  ext i
  simp [Layer]

theorem layer_join {n : Nat} (v w : Vec n) (t : Nat) :
    Layer (fun i => max (v i) (w i)) t = Layer v t ∪ Layer w t := by
  ext i
  simp [Layer]

theorem threshold_injective {n : Nat} {v w : Vec n}
    (h : ∀ t : Nat, Layer v t = Layer w t) : v = w := by
  funext i
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : w i < v i := Nat.lt_of_not_ge hnot
    have hv : i ∈ Layer v (v i) := by
      simp [Layer]
    rw [h (v i)] at hv
    simp [Layer] at hv
    omega
  · by_contra hnot
    have hlt : v i < w i := Nat.lt_of_not_ge hnot
    have hw : i ∈ Layer w (w i) := by
      simp [Layer]
    rw [← h (w i)] at hw
    simp [Layer] at hw
    omega

def Clamp {n : Nat} (d : Nat) (v : Vec n) : Vec n :=
  fun i => min d (v i)

theorem clamp_layer_below {n : Nat} (d t : Nat) (v : Vec n) (ht : t ≤ d) :
    Layer (Clamp d v) t = Layer v t := by
  ext i
  simp only [Clamp, Layer, Set.mem_setOf_eq]
  omega

theorem clamp_layer_above {n : Nat} (d t : Nat) (v : Vec n) (ht : d < t) :
    Layer (Clamp d v) t = ∅ := by
  ext i
  change (t ≤ min d (v i)) ↔ False
  constructor
  · intro h
    have htd : t ≤ d := le_trans h (min_le_left d (v i))
    exact (Nat.not_le_of_lt ht) htd
  · intro h
    exact False.elim h

theorem capped_add_layer {n : Nat} (d t : Nat) (v w : Vec n) (ht : t ≤ d) :
    Layer (Clamp d (fun i => v i + w i)) t =
      CarryCoeff v w t := by
  rw [clamp_layer_below d t (fun i => v i + w i) ht]
  symm
  exact carryCoeff_eq_layer_add v w t

end Imscribing.Stage301_315
