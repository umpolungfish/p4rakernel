import Imscribing.Millennium.SourceBraidSquareCollision

/-! Numerical return specification on the existing IMASM glyph tapes.
The arithmetic equations below are denotations of the native tape operations.
The collision count remains the output required from the source contraction;
these definitions do not substitute a Nat factor engine for that operation. -/
namespace Imscribing.SourceBraidTapeReturn

open Imscribing.SourceBraidSquareCollision

/-- Native numerical cells: EVALT=0 and EVALF=1, least significant first. -/
def payload (n : ℕ) : List Char :=
  n.bits.map (fun b => if b then '⊥' else '⊤')

/-- Read only numerical payloads; an instruction in a payload is rejected. -/
def readPayload : List Char → Option ℕ
  | [] => some 0
  | '⊤' :: tail => (readPayload tail).map (fun n => 2*n)
  | '⊥' :: tail => (readPayload tail).map (fun n => 2*n+1)
  | _ :: _ => none

theorem payload_readback (n : ℕ) : readPayload (payload n) = some n := by
  induction n using Nat.binaryRec' with
  | zero => simp [payload, readPayload]
  | bit b n hn ih =>
    simp only [payload, Nat.bits_append_bit n b hn, List.map_cons]
    cases b <;> simpa [readPayload, payload, Nat.bit_val] using ih

/-- This is the existing morphism_factor::emit_numeral wire format. -/
def emitNumeral (n : ℕ) : List Char :=
  if n = 0 then ['⊢', '⊙', '⊡', '⊣']
  else ['⊢'] ++ (payload n).flatMap (fun b => ['≻', '⋈', '∈', b, '∋']) ++
    ['⊙', '⊡', '⊣']

theorem payload_cells (n : ℕ) : ∀ b ∈ payload n, b = '⊤' ∨ b = '⊥' := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨bit, _, rfl⟩
  cases bit <;> simp

/-- Source, input address, full turns and return remain in one relation. -/
def squareReturn (N x : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (N, x, x*x/N, x*x%N)

theorem square_return_retains (N x : ℕ) :
    (squareReturn N x).1 = N ∧ (squareReturn N x).2.1 = x := ⟨rfl, rfl⟩

theorem square_return_boundary (N x : ℕ) :
    (squareReturn N x).2.2.1 * N + (squareReturn N x).2.2.2 = x*x := by
  dsimp [squareReturn]
  simpa [Nat.mul_comm] using Nat.div_add_mod (x*x) N

/-- Value-level specification of the tape decoder after exact SIC contraction. -/
def factorReadoutValues (N C : ℕ) : ℕ × ℕ :=
  let S := (4*N+1-C)/2
  let h := Nat.sqrt (S*S-4*N)
  ((S-h)/2, (S+h)/2)

def factorPayloads (N C : ℕ) : List Char × List Char :=
  let pair := factorReadoutValues N C
  (payload pair.1, payload pair.2)

def factorWords (N C : ℕ) : List Char × List Char :=
  let pair := factorReadoutValues N C
  (emitNumeral pair.1, emitNumeral pair.2)

theorem readout_from_collision (p q C : ℕ) (hpq : p ≤ q)
    (hC : C + 2*(p+q) = 4*(p*q)+1) :
    factorReadoutValues (p*q) C = (p,q) := by
  have hS : (4*(p*q)+1-C)/2 = p+q := by omega
  have hgap : q-p+p = q := Nat.sub_add_cancel hpq
  have hdisc : (p+q)*(p+q)-4*(p*q) = (q-p)*(q-p) := by
    have h : (p+q)*(p+q) = 4*(p*q)+(q-p)*(q-p) := by nlinarith
    omega
  unfold factorReadoutValues
  simp only [hS, hdisc, Nat.sqrt_eq]
  apply Prod.ext <;> dsimp <;> omega

theorem semiprime_count_boundary (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (hp2 : (2 : ZMod p) ≠ 0)
    (hq2 : (2 : ZMod q) ≠ 0) :
    Fintype.card (SquarePairs (ZMod (p*q))) + 2*(p+q) = 4*(p*q)+1 := by
  have h := semiprime_collision_card p q hpq hp2 hq2
  have hi : (Fintype.card (SquarePairs (ZMod (p*q))) : ℤ) +
      2*((p : ℤ)+q) = 4*((p : ℤ)*q)+1 := by rw [h]; ring
  exact_mod_cast hi

theorem semiprime_readout (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (horder : p ≤ q) (hpq : Nat.Coprime p q)
    (hp2 : (2 : ZMod p) ≠ 0) (hq2 : (2 : ZMod q) ≠ 0) :
    factorReadoutValues (p*q) (Fintype.card (SquarePairs (ZMod (p*q)))) =
      (p,q) :=
  readout_from_collision p q _ horder (semiprime_count_boundary p q hpq hp2 hq2)

theorem semiprime_payload_return (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (horder : p ≤ q) (hpq : Nat.Coprime p q)
    (hp2 : (2 : ZMod p) ≠ 0) (hq2 : (2 : ZMod q) ≠ 0) :
    let tapes := factorPayloads (p*q) (Fintype.card (SquarePairs (ZMod (p*q))))
    readPayload tapes.1 = some p ∧ readPayload tapes.2 = some q := by
  dsimp [factorPayloads]
  rw [semiprime_readout p q horder hpq hp2 hq2]
  exact ⟨payload_readback p, payload_readback q⟩

theorem semiprime_word_return (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (horder : p ≤ q) (hpq : Nat.Coprime p q)
    (hp2 : (2 : ZMod p) ≠ 0) (hq2 : (2 : ZMod q) ≠ 0) :
    factorWords (p*q) (Fintype.card (SquarePairs (ZMod (p*q)))) =
      (emitNumeral p, emitNumeral q) := by
  dsimp [factorWords]
  rw [semiprime_readout p q horder hpq hp2 hq2]

#print axioms payload_readback
#print axioms square_return_boundary
#print axioms semiprime_payload_return
#print axioms semiprime_word_return

end Imscribing.SourceBraidTapeReturn
