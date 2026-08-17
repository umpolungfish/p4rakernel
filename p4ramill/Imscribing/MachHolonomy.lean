/-
  MachHolonomy — the basepoint question, formalised.

  A word is a loop and reading it is transport around that loop. This file makes
  three things precise about that picture and proves them.

  First, transport is a connection: it composes along concatenation, and rotating
  the basepoint does NOT leave the holonomy fixed — it conjugates it. The
  invariant that survives rotation is the abelian image, the signed balance, and
  the difference between "invariant" and "conjugated" is the whole content of
  asking where the loop is read from.

  Second, a word closes exactly when its balance vanishes AND no prefix dips
  below zero. Balance alone is not closure.

  Third — the cycle lemma — a word of balance zero always HAS a rotation that
  closes, and it can be read off: rotate to a point where the prefix balance is
  minimal. So the reading point is not chosen, it is determined by the word. That
  is what makes a canonical basepoint a theorem rather than a convention.
-/
import Mathlib
import Imscribing.FoldVerdict

namespace Imscribing.MachHolonomy

open Imscribing.FoldVerdict Imscribing.FoldVerdict.Mark

/-! ## §1 The connection -/

/-- The signed step: a fork opens, a fuse closes, everything else is carried. -/
def sgn : Mark → ℤ
  | fsplit => 1
  | ffuse  => -1
  | _      => 0

/-- The balance of a word: the abelian image of transport. -/
def bal (w : List Mark) : ℤ := (w.map sgn).sum

/-- The balance after `i` marks. -/
def pre (w : List Mark) (i : ℕ) : ℤ := bal (w.take i)

@[simp] theorem pre_zero (w : List Mark) : pre w 0 = 0 := by simp [pre, bal]

@[simp] theorem pre_cons_succ (m : Mark) (w : List Mark) (i : ℕ) :
    pre (m :: w) (i + 1) = sgn m + pre w i := by
  simp [pre, bal]

/-- Transport along a word from a state. The per-mark action is the connection. -/
def transport (w : List Mark) (s : ℕ × ℕ) : ℕ × ℕ := w.foldl step s

@[simp] theorem transport_nil (s : ℕ × ℕ) : transport [] s = s := rfl

@[simp] theorem transport_cons (m : Mark) (w : List Mark) (s : ℕ × ℕ) :
    transport (m :: w) s = transport w (step s m) := rfl

/-- **Transport composes along concatenation.** -/
theorem transport_append (v w : List Mark) (s : ℕ × ℕ) :
    transport (v ++ w) s = transport w (transport v s) := by
  simp [transport, List.foldl_append]

@[simp] theorem bal_append (v w : List Mark) : bal (v ++ w) = bal v + bal w := by
  simp [bal]

/-- **Rotation conjugates the holonomy.** Cutting the loop at a different point
does not fix transport; it intertwines the two readings. Writing the loop as
`v ++ t`, the reading from the other cut satisfies this identity, and there is no
identity saying the two transports are equal. -/
theorem transport_rotate_intertwine (v t : List Mark) (s : ℕ × ℕ) :
    transport (t ++ v) (transport v s) = transport v (transport (v ++ t) s) := by
  simp [transport_append]

/-- **The abelian image is rotation-invariant.** This is what survives the
basepoint, and it survives because it factors through a permutation. -/
theorem bal_rotate (w : List Mark) (k : ℕ) : bal (w.rotate k) = bal w := by
  have hp : (w.rotate k).Perm w := List.rotate_perm w k
  simpa [bal] using (hp.map sgn).sum_eq

/-! ## §2 Closure, and what rotation moves -/

/-- A word closes when its balance vanishes and no prefix dips below zero.
Balance alone is not closure — that is the distinction between an invariant that
survives rotation and a walk that returns. -/
def Closes (w : List Mark) : Prop := bal w = 0 ∧ ∀ i, 0 ≤ pre w i

/-- **The invariant survives rotation.** -/
theorem closes_bal_rotate (w : List Mark) (k : ℕ) : bal (w.rotate k) = bal w :=
  bal_rotate w k

/-- **Transport does not.** A fork then a fuse closes; the same two marks in the
other order do not, and the two words are rotations of one another. The register
is moved by the basepoint while the balance is not. -/
theorem transport_not_rotation_invariant :
    transport [fsplit, ffuse] (0, 0) ≠ transport ([fsplit, ffuse].rotate 1) (0, 0) := by
  decide

theorem bal_is_rotation_invariant_here :
    bal [fsplit, ffuse] = bal ([fsplit, ffuse].rotate 1) := by decide

/-- The failing rotation is the one that dips: closure is lost at the prefix,
not at the total. -/
theorem rotation_dips :
    bal [ffuse, fsplit] = 0 ∧ ¬ (∀ i, 0 ≤ pre [ffuse, fsplit] i) := by
  refine ⟨by decide, fun h => ?_⟩
  have := h 1
  simp [pre, bal, sgn] at this

/-! ## §3 The cycle lemma: the reading point is determined -/

/-- Prefix balances of a rotation, before the wrap. -/
theorem pre_rotate_lt (w : List Mark) (k i : ℕ) (hk : k ≤ w.length)
    (hi : i ≤ w.length - k) :
    pre (w.rotate k) i = pre w (k + i) - pre w k := by
  have hrot : w.rotate k = w.drop k ++ w.take k := List.rotate_eq_drop_append_take hk
  have hlen : (w.drop k).length = w.length - k := by simp
  have htake : (w.rotate k).take i = (w.drop k).take i := by
    rw [hrot, List.take_append_of_le_length (by omega)]
  have hsplit : w.take (k + i) = w.take k ++ (w.drop k).take i := List.take_add
  simp only [pre, htake, hsplit, bal_append]
  ring

/-- Prefix balances of a rotation, after the wrap, when the loop closes. -/
theorem pre_rotate_ge (w : List Mark) (k i : ℕ) (hk : k ≤ w.length)
    (hb : bal w = 0) (hi : w.length - k ≤ i) (hile : i ≤ w.length) :
    pre (w.rotate k) i = pre w (i - (w.length - k)) - pre w k := by
  have hrot : w.rotate k = w.drop k ++ w.take k := List.rotate_eq_drop_append_take hk
  have hlen : (w.drop k).length = w.length - k := by simp
  have htake : (w.rotate k).take i
      = w.drop k ++ (w.take k).take (i - (w.length - k)) := by
    rw [hrot, List.take_append, List.take_of_length_le (by omega), hlen]
  have hdrop : bal (w.drop k) = bal w - pre w k := by
    have h := congrArg bal (List.take_append_drop k w).symm
    simp only [bal_append] at h
    simp only [pre]
    omega
  have hkk : (w.take k).take (i - (w.length - k)) = w.take (i - (w.length - k)) := by
    rw [List.take_take]
    congr 1
    omega
  simp only [pre, htake, bal_append, hdrop, hkk, hb]
  ring

/-- **The cycle lemma.** A word of balance zero has a rotation that closes, and
the rotation is read off the word: cut where the prefix balance is least. The
reading point is determined by the word, not chosen for it. -/
theorem cycle_lemma (w : List Mark) (hb : bal w = 0) :
    ∃ k ≤ w.length, ∀ i, 0 ≤ pre (w.rotate k) i := by
  classical
  obtain ⟨k, hkmem, hkmin⟩ :=
    Finset.exists_min_image (Finset.range (w.length + 1)) (fun j => pre w j)
      ⟨0, Finset.mem_range.2 (by omega)⟩
  have hk : k ≤ w.length := by
    have := Finset.mem_range.1 hkmem; omega
  refine ⟨k, hk, fun i => ?_⟩
  by_cases hile : i ≤ w.length
  · by_cases hlt : i ≤ w.length - k
    · rw [pre_rotate_lt w k i hk hlt]
      have := hkmin (k + i) (Finset.mem_range.2 (by omega))
      omega
    · rw [pre_rotate_ge w k i hk hb (by omega) hile]
      have := hkmin (i - (w.length - k)) (Finset.mem_range.2 (by omega))
      omega
  · have hlen : (w.rotate k).length = w.length := by simp
    have hall : (w.rotate k).take i = w.rotate k :=
      List.take_of_length_le (by omega)
    rw [pre, hall, bal_rotate, hb]

/-- **Closure at the determined point.** Balance zero is not merely necessary
for a loop to close somewhere — it is sufficient, once the loop is read where
the word says to read it. -/
theorem closes_at_min (w : List Mark) (hb : bal w = 0) :
    ∃ k ≤ w.length, Closes (w.rotate k) := by
  obtain ⟨k, hk, hmin⟩ := cycle_lemma w hb
  exact ⟨k, hk, ⟨by rw [bal_rotate]; exact hb, hmin⟩⟩

/-! ## §4 A power of sixteen is a congruence, not a signature

The conductor generator at `d = 2^n` is `2^(n+1)`. That is a power of sixteen
exactly when `n ≡ 3 (mod 4)`, which is why the values `16, 16², 16³, 16⁴` appear
at `d = 8, 128, 2048, 32768` — one family carried by one congruence. The exponent
counts `n`, so no single member of the family carries meaning the others do not.
-/

theorem sixteen_power_iff (n : ℕ) :
    (∃ k : ℕ, 2 ^ (n + 1) = 16 ^ k) ↔ (n + 1) % 4 = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    have h16 : (16 : ℕ) ^ k = 2 ^ (4 * k) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    rw [h16] at hk
    have := Nat.pow_right_injective (le_refl 2) hk
    omega
  · intro h
    refine ⟨(n + 1) / 4, ?_⟩
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 1
    omega

/-- The family, at the four dimensions where it has been read. -/
theorem sixteen_family :
    (2 ^ (3 + 1) = 16 ^ 1) ∧ (2 ^ (7 + 1) = 16 ^ 2) ∧
    (2 ^ (11 + 1) = 16 ^ 3) ∧ (2 ^ (15 + 1) = 16 ^ 4) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms transport_rotate_intertwine
#print axioms transport_not_rotation_invariant
#print axioms cycle_lemma
#print axioms sixteen_power_iff

end Imscribing.MachHolonomy
