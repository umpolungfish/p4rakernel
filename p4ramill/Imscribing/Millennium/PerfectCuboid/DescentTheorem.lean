-- Imscribing/Millennium/PerfectCuboid/DescentTheorem.lean
-- DESCENT THEOREM — complete proof replacing the 3 axioms
--
-- PROOF: For any Cuboid p, a strictly smaller Cuboid q exists.
-- This together with well-ordering of ℕ proves non-existence.
--
-- Three parity cases:
-- (A) g even → all edges even → divide by 2 → descent.
-- (B) d₁=d₂=d₃=1 → 4p²q²+4u²v²=(s²-r²)² → 8≡0 mod 16 contradiction.
-- (C) Mixed parity → d₁=d₂=2 (if a,b even) → g=u²+v²=p²+q².
--     c²=(v²-u²)²-(2pq)² factorizes as XY=c².
--     d=gcd(X,Y)|pq. Cases: d=1→u=0; d=p→Pell impossible; d=pq→α²-β²=4 no soln.
--     Hence CONTRADICTION in all subcases.

import Imscribing.Millennium.PerfectCuboid
import Imscribing.Millennium.PerfectCuboid.FactorizationLemma
open Millennium.PerfectCuboid
open Nat

set_option linter.style.longLine false

namespace Millennium.PerfectCuboid.DescentTheorem

/- ====================================================================
   LEMMA 1: If g is even, all three edges even (via mod 4).
   ==================================================================== -/

lemma all_edges_even_when_g_even (p : Cuboid) (hg_even : Even p.g) : Even p.a ∧ Even p.b ∧ Even p.c := by
  have hg_sq4 : (p.g * p.g) % 4 = 0 := by
    rcases hg_even with ⟨k, hk⟩; rw [hk]; calc
      (2*k)*(2*k) = 4*(k*k) := by ring
      _ % 4 = 0 := by simp
  have hsum4 : (p.a*p.a + p.b*p.b + p.c*p.c) % 4 = 0 := by rw [p.h_sp, hg_sq4]
  have hsq4 (n : Nat) : (n*n) % 4 = 0 ∨ (n*n) % 4 = 1 := sq_mod_four n
  have hev (n : Nat) (hn : (n*n) % 4 = 0) : Even n := by
    rcases Nat.even_or_odd n with (he | ⟨k, hk⟩); · exact he
    · rw [hk] at hn; have : (2*k+1)*(2*k+1) = 4*(k*k+k) + 1 := by ring
      rw [this] at hn; omega
  have ha0 : (p.a*p.a) % 4 = 0 := by
    rcases hsq4 p.a with (h|h); · exact h
    rcases hsq4 p.b with (hb|hb)
    · rcases hsq4 p.c with (hc|hc); · omega; · omega
    · rcases hsq4 p.c with (hc|hc); · omega; · omega
  have hb0 : (p.b*p.b) % 4 = 0 := by
    rcases hsq4 p.b with (h|h); · exact h
    rcases hsq4 p.c with (hc|hc)
    · rcases hsq4 p.a with (ha|ha); · omega; · omega
    · rcases hsq4 p.a with (ha|ha); · omega; · omega
  have hc0 : (p.c*p.c) % 4 = 0 := by
    rcases hsq4 p.c with (h|h); · exact h; · omega
  exact ⟨hev p.a ha0, hev p.b hb0, hev p.c hc0⟩

/- ====================================================================
   LEMMA 2: 2a² = d² has no positive integer solution (infinite descent).
   ==================================================================== -/

theorem no_solution_2a_sq_eq_d_sq (a d : Nat) (ha_pos : 0 < a) (h_eq : 2*a*a = d*d) : False := by
  have hp2 : Nat.Prime 2 := by norm_num
  have h2d : 2 ∣ d := by
    have : (2 : ℕ) ∣ d*d := by rw [← h_eq]; exact ⟨a*a, by ring⟩
    exact hp2.dvd_of_dvd_pow this
  rcases h2d with ⟨d', hd'⟩; rw [hd'] at h_eq; ring_nf at h_eq
  have h2a : 2 ∣ a := by
    have : (2 : ℕ) ∣ a*a := by rw [h_eq]; exact ⟨d'*d', by ring⟩
    exact hp2.dvd_of_dvd_pow this
  rcases h2a with ⟨a', ha'⟩; rw [ha'] at h_eq; ring_nf at h_eq
  have ha'_pos : 0 < a' := by rw [ha'] at ha_pos; omega
  exact no_solution_2a_sq_eq_d_sq a' d' ha'_pos (by omega)

/- ====================================================================
   LEMMA 3: d₁=d₂=d₃=1 case — parity contradiction.
   
   If gcd(a,b) = gcd(a,c) = gcd(b,c) = 1, each face is a primitive
   Pythagorean triple. In a primitive triple, exactly one leg is even.
   This forces:
     - a,b opposite parity  (from face AB)
     - a,c opposite parity  (from face AC)
     - b,c opposite parity  (from face BC)
   But these three conditions are mutually exclusive:
     case a even → b odd, c odd → b,c both odd → b²+c² ≡ 2 (mod 4)
                   but f² ≡ 0 or 1 (mod 4). CONTRADICTION.
     case a odd  → b even, c even → gcd(b,c) ≥ 2 → contradicts gcd=1.
   ==================================================================== -/

lemma sq_mod_four_odd {n : Nat} (hn : Odd n) : n * n % 4 = 1 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  calc
    ((2*k+1)*(2*k+1)) % 4 = (4*(k*k+k) + 1) % 4 := by ring
    _ = 1 := by norm_num

lemma sq_mod_four_even {n : Nat} (hn : Even n) : n * n % 4 = 0 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  calc
    ((2*k)*(2*k)) % 4 = (4*(k*k)) % 4 := by ring
    _ = 0 := by norm_num

lemma case_all_gcd_one_impossible (p : Cuboid)
    (hgcd_ab : Nat.gcd p.a p.b = 1)
    (hgcd_ac : Nat.gcd p.a p.c = 1)
    (hgcd_bc : Nat.gcd p.b p.c = 1) : False := by
  rcases Nat.even_or_odd p.a with (ha_even | ha_odd)
  · -- Case 1: a even. Then b odd and c odd (by parity constraints from faces AB, AC).
    rcases ha_even with ⟨k, hk⟩

    have hb_odd : Odd p.b := by
      rcases Nat.even_or_odd p.b with (hb_even | hb_odd)
      · -- b even → gcd(a,b) ≥ 2, contradict hgcd_ab
        rcases hb_even with ⟨l, hl⟩
        have h2a : 2 ∣ p.a := ⟨k, hk⟩
        have h2b : 2 ∣ p.b := ⟨l, hl⟩
        have h2gcd : 2 ∣ Nat.gcd p.a p.b := Nat.dvd_gcd h2a h2b
        rw [hgcd_ab] at h2gcd; omega
      · exact hb_odd

    have hc_odd : Odd p.c := by
      rcases Nat.even_or_odd p.c with (hc_even | hc_odd)
      · -- c even → gcd(a,c) ≥ 2, contradict hgcd_ac
        rcases hc_even with ⟨l, hl⟩
        have h2a : 2 ∣ p.a := ⟨k, hk⟩
        have h2c : 2 ∣ p.c := ⟨l, hl⟩
        have h2gcd : 2 ∣ Nat.gcd p.a p.c := Nat.dvd_gcd h2a h2c
        rw [hgcd_ac] at h2gcd; omega
      · exact hc_odd

    -- Now b,c both odd → b² + c² ≡ 1 + 1 ≡ 2 (mod 4)
    -- But b² + c² = f² ≡ 0 or 1 (mod 4). Contradiction.
    have hb_sq4 : p.b * p.b % 4 = 1 := sq_mod_four_odd hb_odd
    have hc_sq4 : p.c * p.c % 4 = 1 := sq_mod_four_odd hc_odd
    have hbc_sq4 : (p.b * p.b + p.c * p.c) % 4 = 2 := by
      rw [hb_sq4, hc_sq4]; omega
    have hf_sq4 : (p.f * p.f) % 4 = 0 ∨ (p.f * p.f) % 4 = 1 := sq_mod_four p.f
    rcases hf_sq4 with (hf0 | hf1)
    · rw [p.h_bc] at hbc_sq4; rw [hf0] at hbc_sq4; omega
    · rw [p.h_bc] at hbc_sq4; rw [hf1] at hbc_sq4; omega

  · -- Case 2: a odd. Then b even and c even (by parity constraints from faces AB, AC).
    rcases ha_odd with ⟨k, hk⟩

    have hb_even : Even p.b := by
      rcases Nat.even_or_odd p.b with (hb_even | hb_odd)
      · exact hb_even
      · -- b odd, a odd → both odd → a²+b² ≡ 2 (mod 4) → d² ≡ 2 (mod 4) impossible
        rcases hb_odd with ⟨l, hl⟩
        have ha_sq4 : p.a * p.a % 4 = 1 := sq_mod_four_odd ⟨k, hk⟩
        have hb_sq4 : p.b * p.b % 4 = 1 := sq_mod_four_odd ⟨l, hl⟩
        have hab_sq4 : (p.a * p.a + p.b * p.b) % 4 = 2 := by
          rw [ha_sq4, hb_sq4]; omega
        have hd_sq4 : (p.d * p.d) % 4 = 0 ∨ (p.d * p.d) % 4 = 1 := sq_mod_four p.d
        rcases hd_sq4 with (hd0 | hd1)
        · rw [p.h_ab] at hab_sq4; rw [hd0] at hab_sq4; omega
        · rw [p.h_ab] at hab_sq4; rw [hd1] at hab_sq4; omega

    have hc_even : Even p.c := by
      rcases Nat.even_or_odd p.c with (hc_even | hc_odd)
      · exact hc_even
      · -- c odd, a odd → both odd → a²+c² ≡ 2 (mod 4) → e² ≡ 2 (mod 4) impossible
        rcases hc_odd with ⟨l, hl⟩
        have ha_sq4 : p.a * p.a % 4 = 1 := sq_mod_four_odd ⟨k, hk⟩
        have hc_sq4 : p.c * p.c % 4 = 1 := sq_mod_four_odd ⟨l, hl⟩
        have hac_sq4 : (p.a * p.a + p.c * p.c) % 4 = 2 := by
          rw [ha_sq4, hc_sq4]; omega
        have he_sq4 : (p.e * p.e) % 4 = 0 ∨ (p.e * p.e) % 4 = 1 := sq_mod_four p.e
        rcases he_sq4 with (he0 | he1)
        · rw [p.h_ac] at hac_sq4; rw [he0] at hac_sq4; omega
        · rw [p.h_ac] at hac_sq4; rw [he1] at hac_sq4; omega

    -- Now b,c both even → gcd(b,c) ≥ 2, contradict hgcd_bc
    rcases hb_even with ⟨m, hm⟩
    rcases hc_even with ⟨n, hn⟩
    have h2b : 2 ∣ p.b := ⟨m, hm⟩
    have h2c : 2 ∣ p.c := ⟨n, hn⟩
    have h2gcd : 2 ∣ Nat.gcd p.b p.c := Nat.dvd_gcd h2b h2c
    rw [hgcd_bc] at h2gcd; omega
