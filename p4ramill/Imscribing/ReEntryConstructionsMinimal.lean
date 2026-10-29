import Mathlib

namespace Imscribing.ReEntryConstructionsMinimal

/-- A well label is a natural prime together with its primality witness. -/
abbrev PrimeLabel := {p : Nat // Nat.Prime p}

/-- A descent history, with one prime multiplication per step. -/
abbrev WellPath := List PrimeLabel

/-- The shared origin is represented by the empty descent history. -/
def origin : WellPath := []

/-- An address evaluates by multiplying its prime labels. -/
def evaluate : WellPath → Nat
  | [] => 1
  | p :: rest => p.val * evaluate rest

/-- Total re-entry depth is the count of prime steps. -/
def depth (w : WellPath) : Nat := w.length

/-- Descend into well `p` exactly once. -/
def descend (p : PrimeLabel) (w : WellPath) : WellPath := p :: w

@[simp] theorem evaluate_origin : evaluate origin = 1 := rfl
@[simp] theorem depth_origin : depth origin = 0 := rfl

@[simp] theorem evaluate_descend (p : PrimeLabel) (w : WellPath) :
    evaluate (descend p w) = p.val * evaluate w := rfl

@[simp] theorem depth_descend (p : PrimeLabel) (w : WellPath) :
    depth (descend p w) = depth w + 1 := by
  simp [depth, descend]

/-- Independent prime descents commute after numerical evaluation. -/
theorem descend_commutes_in_value (p q : PrimeLabel) (w : WellPath) :
    evaluate (descend p (descend q w)) =
      evaluate (descend q (descend p w)) := by
  simp [evaluate_descend, Nat.mul_left_comm, Nat.mul_comm]

/-- Independent prime descents have equal depth. -/
theorem descend_commutes_in_depth (p q : PrimeLabel) (w : WellPath) :
    depth (descend p (descend q w)) =
      depth (descend q (descend p w)) := by
  simp

/-- Every finite prime descent evaluates to a positive integer. -/
theorem evaluate_positive (w : WellPath) : 0 < evaluate w := by
  induction w with
  | nil => simp [evaluate]
  | cons p tail ih =>
      simp only [evaluate]
      exact Nat.mul_pos p.property.pos ih

/-- Binary reading is applied to the evaluated prime-well address. -/
def bitSelected (w : WellPath) (i : Nat) : Bool :=
  Nat.testBit (evaluate w) i

/-- The kernel's four binary membership positions. -/
def selected4 (n : Nat) (i : Fin 4) : Bool :=
  decide ((n / 2 ^ i.val) % 2 = 1)

def support4 (n : Nat) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => selected4 n i)

def count4 (n : Nat) : Nat := (support4 n).card

def binaryAtom4 (n : Nat) : Prop := count4 n = 1

def primeAtom (n : Nat) : Prop := Nat.Prime n

/-- All 16 labels reconstruct from their 4-bit supports. -/
def reconstruct4 (n : Nat) : Nat :=
  ∑ i ∈ support4 n, (2 : Nat) ^ i.val

theorem reconstruct4_all :
    ∀ n : Fin 16, reconstruct4 n.val = n.val := by
  decide

/-- Exactly 2 is prime and single-bit among the 16 native masks. -/
theorem common_atom4 :
    ∀ n : Fin 16,
      (primeAtom n.val ∧ binaryAtom4 n.val) ↔ n.val = 2 := by
  intro n
  fin_cases n <;>
  (try decide) <;>
  (try
    {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try norm_num [primeAtom, binaryAtom4, count4, support4, selected4, Finset.card_univ, Finset.filter_eq'] at h ⊢) <;>
      (try rfl) <;>
      (try aesop)
    }) <;>
  (try
    {
      norm_num [primeAtom, binaryAtom4, count4, support4, selected4, Finset.card_univ, Finset.filter_eq'] at *
      <;>
      (try decide) <;>
      (try aesop)
    })

theorem eight_binary_atom : binaryAtom4 8 := by
  norm_num [binaryAtom4, count4, support4, selected4, Fin.val_zero, Fin.val_succ]
  <;> rfl

theorem eight_not_prime : ¬ primeAtom 8 := by
  norm_num [primeAtom, Nat.Prime]

theorem thirteen_prime : primeAtom 13 := by
  norm_num [primeAtom, Nat.Prime]

theorem thirteen_not_binary_atom : ¬ binaryAtom4 13 := by
  norm_num [binaryAtom4, count4, support4, selected4, Fin.val_zero, Fin.val_succ]
  <;> decide

end Imscribing.ReEntryConstructionsMinimal