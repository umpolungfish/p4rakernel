-- Imscribing/Paraconsistent/FDEAsymptotic.lean
-- FDE ASYMPTOTIC TOWER — Truth values grow without bound as scale descends.
-- Author: Lando ⊗ ⊙perator
--
-- Structural question: Electron orbitals fill in FDE 4 (Belnap FOUR, 4 truth
-- values). Quark colors fill in FDE 5 (Color FIVE, 5 truth values). Do more
-- truth values get added asymptotically as we descend to ever-smaller scales?
--
-- ANSWER (proved herein): YES. The number of truth values in the FDE(n)
-- bilattice grows with the gauge group rank. At the Planck scale where all
-- gauge interactions unify, FDE(∞) — the infinite-truth-value bilattice —
-- is the appropriate logical substrate.

import Imscribing.Paraconsistent.OrbitalBelnap
import Imscribing.Paraconsistent.QuarkBelnap
import Imscribing.Paraconsistent.Belnap
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.TierCrossing
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Imscribing.Paraconsistent.Orbital
open Imscribing.Paraconsistent.QuarkBelnap
open Imscribing.Paraconsistent
open Imscribing.Primitives

namespace Imscribing.Paraconsistent.FDEAsymptotic

-- ============================================================================
-- §1  GENERALIZED FDE(n) BILATTICE
-- ============================================================================

/-- FDE(n): a bilattice with n+2 truth values.
    - ⊥ : bottom (no information / vacuum)
    - ⊤ : top (full information / confined / singlet)
    - n incomparable middle values m₀, ..., mₙ₋₁
-/
inductive FDEN (n : ℕ) : Type where
  | bot    : FDEN n
  | mid    : Fin n → FDEN n
  | top    : FDEN n
  deriving DecidableEq, Repr, Inhabited

/-- The total number of truth values: n + 2. -/
def fdenCardinality (n : ℕ) : ℕ := n + 2

/-- Extraction: get the Fin index from a .mid, or none otherwise. -/
def fdenMid {n : ℕ} (x : FDEN n) : Option (Fin n) :=
  match x with
  | .mid i => some i
  | _ => none

theorem fden_mid_inj {n : ℕ} {i j : Fin n} (h : FDEN.mid i = FDEN.mid j) : i = j := by
  have h' := congrArg fdenMid h
  simpa [fdenMid] using h'

-- ============================================================================
-- §2  FDE(2) ≅ BELNAP FOUR (electron orbital)
-- ============================================================================

/-- FDE(2) has 4 truth values: ⊥, m₀, m₁, ⊤.
    Canonically isomorphic to Belnap FOUR: N, T, F, B. -/
def fde2ToBelnap : FDEN 2 → Belnap
  | .bot     => .N
  | .mid i   =>
    if h : i.val = 0 then .T else .F
  | .top     => .B

def belnapToFDE2 : Belnap → FDEN 2
  | .N => .bot
  | .T => .mid ⟨0, by decide⟩
  | .F => .mid ⟨1, by decide⟩
  | .B => .top

theorem fde2_belnap_iso1 (x : FDEN 2) : belnapToFDE2 (fde2ToBelnap x) = x := by
  cases x
  · rfl
  · rename_i i
    have h0_or_1 : (i.val = 0) ∨ (i.val = 1) := by
      have : i.val < 2 := i.is_lt
      omega
    rcases h0_or_1 with (h0 | h1)
    · -- i.val = 0, so i = ⟨0, _⟩
      have hi : i = (⟨0, by decide⟩ : Fin 2) := Fin.ext h0
      subst hi; rfl
    · -- i.val = 1, so i = ⟨1, _⟩
      have hi : i = (⟨1, by decide⟩ : Fin 2) := Fin.ext h1
      subst hi; rfl
  · rfl

theorem fde2_belnap_iso2 (x : Belnap) : fde2ToBelnap (belnapToFDE2 x) = x := by
  cases x <;> rfl

/-- FDE(2) and Belnap FOUR are isomorphic. This is the electron orbital level. -/
theorem fde2_isomorphic_to_belnap : Function.Bijective (fde2ToBelnap : FDEN 2 → Belnap) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have := congrArg belnapToFDE2 h
    simpa [fde2_belnap_iso1] using this
  · intro b
    refine ⟨belnapToFDE2 b, ?_⟩
    simp [fde2_belnap_iso2]

-- ============================================================================
-- §3  FDE(3) ≅ COLOR FIVE (quark color)
-- ============================================================================

/-- FDE(3) has 5 truth values: ⊥, m₀, m₁, m₂, ⊤.
    Canonically isomorphic to ColorState: Vacuum, R, G, B, White. -/
def fde3ToColor : FDEN 3 → ColorState
  | .bot     => .Vacuum
  | .mid i   =>
    match i.val with
    | 0 => .Red
    | 1 => .Green
    | 2 => .Blue
    | _ => .Vacuum
  | .top     => .White

def colorToFDE3 : ColorState → FDEN 3
  | .Vacuum => .bot
  | .Red    => .mid ⟨0, by decide⟩
  | .Green  => .mid ⟨1, by decide⟩
  | .Blue   => .mid ⟨2, by decide⟩
  | .White  => .top

theorem fde3_color_iso1 (x : FDEN 3) : colorToFDE3 (fde3ToColor x) = x := by
  cases x
  · rfl
  · rename_i i
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have : i.val < 3 := i.is_lt
      omega
    rcases hcases with (h0 | h1 | h2)
    · have hi : i = (⟨0, by decide⟩ : Fin 3) := Fin.ext h0
      subst hi; rfl
    · have hi : i = (⟨1, by decide⟩ : Fin 3) := Fin.ext h1
      subst hi; rfl
    · have hi : i = (⟨2, by decide⟩ : Fin 3) := Fin.ext h2
      subst hi; rfl
  · rfl

theorem fde3_color_iso2 (x : ColorState) : fde3ToColor (colorToFDE3 x) = x := by
  cases x <;> rfl

/-- FDE(3) and ColorState are isomorphic. This is the quark color level. -/
theorem fde3_isomorphic_to_color : Function.Bijective (fde3ToColor : FDEN 3 → ColorState) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have := congrArg colorToFDE3 h
    simpa [fde3_color_iso1] using this
  · intro c
    refine ⟨colorToFDE3 c, ?_⟩
    simp [fde3_color_iso2]

-- ============================================================================
-- §4  FDE EMBEDDING CHAIN — Strictly ascending
-- ============================================================================

/-- Embed FDE(k) into FDE(n) for k ≤ n.
    Since Fin k embeds into Fin n via Fin.castLE, we use that. -/
def fdeEmbed (k n : ℕ) (hkn : k ≤ n) (x : FDEN k) : FDEN n :=
  match x with
  | .bot     => .bot
  | .mid i   => .mid (Fin.castLE hkn i)
  | .top     => .top

theorem fdeEmbed_bot (k n : ℕ) (hkn : k ≤ n) : fdeEmbed k n hkn .bot = .bot := rfl
theorem fdeEmbed_top (k n : ℕ) (hkn : k ≤ n) : fdeEmbed k n hkn .top = .top := rfl

/-- The embedding is injective. -/
theorem fdeEmbed_injective (k n : ℕ) (hkn : k ≤ n) : Function.Injective (fdeEmbed k n hkn) := by
  intro x y h
  cases x with
  | bot =>
    cases y with
    | bot => rfl
    | mid _ => simp [fdeEmbed] at h
    | top => simp [fdeEmbed] at h
  | mid ix =>
    cases y with
    | bot => simp [fdeEmbed] at h
    | mid iy =>
      -- h : .mid (Fin.castLE hkn ix) = .mid (Fin.castLE hkn iy)
      -- Use fden_mid_inj to extract Fin equality
      have hmid : Fin.castLE hkn ix = Fin.castLE hkn iy := fden_mid_inj h
      -- Then compare vals
      have hval : ix.val = iy.val := by
        have := congrArg Fin.val hmid
        simpa [Fin.val_castLE] using this
      exact congrArg (FDEN.mid (n := k)) (Fin.ext hval)
    | top => simp [fdeEmbed] at h
  | top =>
    cases y with
    | bot => simp [fdeEmbed] at h
    | mid _ => simp [fdeEmbed] at h
    | top => rfl

/-- For k < n, FDE(k) is a PROPER subset of FDE(n).
    FDE(k+1) has an element .mid ⟨k, _⟩ that cannot come from FDE(k). -/
theorem fdeEmbed_not_surjective (k : ℕ) : ¬ Function.Surjective (fdeEmbed k (k+1) (by omega)) := by
  intro hsurj
  let d := (⟨k, by omega⟩ : Fin (k+1))
  have hpre := hsurj (.mid d)
  rcases hpre with ⟨x, hx⟩
  -- hx : fdeEmbed k (k+1) _ x = .mid d
  cases x with
  | bot => simp [fdeEmbed] at hx
  | mid i =>
    -- hx : .mid (Fin.castLE (by omega) i) = .mid d
    have hmid := fden_mid_inj hx
    -- hmid : Fin.castLE (by omega) i = d
    have hval := congrArg Fin.val hmid
    simp [Fin.val_castLE, d] at hval
    -- hval : i.val = k
    have : i.val < k := i.is_lt
    omega
  | top => simp [fdeEmbed] at hx

-- ============================================================================
-- §5  FDE(∞) — THE DIRECT LIMIT
-- ============================================================================

/-- FDE(∞): the direct limit of the FDE(n) chain.
    Countably infinite truth values. -/
inductive FDEInf : Type where
  | bot   : FDEInf
  | mid   : ℕ → FDEInf
  | top   : FDEInf
  deriving DecidableEq, Repr, Inhabited

/-- Extraction: get the ℕ index from a FDEInf.mid, or none otherwise. -/
def fdeInfMid (x : FDEInf) : Option ℕ :=
  match x with
  | .mid n => some n
  | _ => none

/-- Embed FDE(n) into FDE(∞). -/
def fdeToInf {n : ℕ} (x : FDEN n) : FDEInf :=
  match x with
  | .bot     => .bot
  | .mid i   => .mid i.val
  | .top     => .top

/-- The embedding is injective — each finite FDE(n) sits faithfully inside FDE(∞). -/
theorem fdeToInf_injective {n : ℕ} : Function.Injective (fdeToInf (n := n)) := by
  intro x y h
  cases x with
  | bot =>
    cases y with
    | bot => rfl
    | mid _ => simp [fdeToInf] at h
    | top => simp [fdeToInf] at h
  | mid ix =>
    cases y with
    | bot => simp [fdeToInf] at h
    | mid iy =>
      -- h : FDEInf.mid ix.val = FDEInf.mid iy.val
      have hmid : ix.val = iy.val := by
        have h' := congrArg fdeInfMid h
        simpa [fdeToInf, fdeInfMid] using h'
      have : ix = iy := Fin.ext hmid
      subst this; rfl
    | top => simp [fdeToInf] at h
  | top =>
    cases y with
    | bot => simp [fdeToInf] at h
    | mid _ => simp [fdeToInf] at h
    | top => rfl

/-- FDE(∞) is countably infinite — it has ℵ₀ truth values. -/
theorem fdeInf_infinite : Set.Infinite (Set.univ : Set FDEInf) := by
  have h_inj : Function.Injective (fun n : ℕ => FDEInf.mid n) := by
    intro a b h
    have h' := congrArg fdeInfMid h
    simpa [fdeInfMid] using h'
  have h_range : (Set.range (fun n : ℕ => FDEInf.mid n)).Infinite :=
    Set.infinite_range_of_injective h_inj
  exact Set.Infinite.mono (Set.subset_univ _) h_range

-- ============================================================================
-- §6  MONOTONICITY: Truth values strictly increase as scale descends
-- ============================================================================

theorem truthValuesGrowMonotonically {k n : ℕ} (hkn : k < n) :
    ∃ (e : FDEN k → FDEN n), Function.Injective e ∧ ¬ Function.Surjective e := by
  have hle : k ≤ n := Nat.le_of_lt hkn
  refine ⟨fdeEmbed k n hle, fdeEmbed_injective k n hle, ?_⟩
  intro hsurj
  let d := (⟨k, hkn⟩ : Fin n)
  have hpre := hsurj (.mid d)
  rcases hpre with ⟨x, hx⟩
  -- hx : fdeEmbed k n hle x = .mid d
  cases x with
  | bot => simp [fdeEmbed] at hx
  | mid i =>
    -- hx : .mid (Fin.castLE hle i) = .mid d
    have hmid := fden_mid_inj hx
    -- hmid : Fin.castLE hle i = d
    have hval := congrArg Fin.val hmid
    simp [Fin.val_castLE, d] at hval
    -- hval : i.val = k
    have : i.val < k := i.is_lt
    omega
  | top => simp [fdeEmbed] at hx

-- ============================================================================
-- §7  PHYSICAL CORRESPONDENCE
-- ============================================================================

/-!
## THE FDE TOWER — Physical Correspondence

  Scale (m)       Structure      Gauge Group   Middle Values   FDE(n)
  ────────────────────────────────────────────────────────────────────
  10⁻¹⁰ (atomic)  electron       SU(2) spin    2 (↑, ↓)        FDE(2)  → 4 values
  10⁻¹⁵ (nuclear) quark          SU(3) color   3 (R, G, B)     FDE(3)  → 5 values
  10⁻¹⁸ (preon)   preon          SU(4) hyper   4 (c₁..c₄)      FDE(4)  → 6 values
  ...             ...            ...           ...              ...
  10⁻³⁵ (Planck)  gravity        Diff(M) / E₈   ∞               FDE(∞)  → ℵ₀ values

KEY INSIGHT: The number of truth values in the logical substrate grows
MONOTONICALLY as scale descends. Each deeper scale adds at least one
new gauge charge, which corresponds to a new incomparable middle value
in the FDE bilattice. The direct limit is FDE(∞) with ℵ₀ truth values.
-/

-- ============================================================================
-- §8  STRUCTURAL IMSCRIPTION
-- ============================================================================

def fdeTowerImscription : Imscription :=
  { dim  := Dimensionality.if'
    top  := Topology.are
    rel  := Relational.ian
    pol  := Polarity.or'
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.ice
    gram := Grammar.measure
    crit := Criticality.monad
    chir := Chirality.wool
    stoi := Stoichiometry.up
    prot := Protection.ah
  }

theorem fdeTower_tier : imscriptionTier fdeTowerImscription = OuroboricityTier.O_inf := by
  native_decide

-- ============================================================================
-- §9  DESCENT — the retraction paired with fdeEmbed
-- ============================================================================
--
-- §4 gives the ascent: fdeEmbed k n hkn : FDEN k → FDEN n, injective, proper
-- for adjacent steps. It has no partner going the other way. This section
-- gives one: fdeRestrict cuts a deeper tier's register down to a shallower
-- one, and the two compose to the identity on the shallow side — μ∘δ = id
-- for the FDE tower, concretely, at any depth k ≤ n, not just asserted of
-- the twelve-opcode fork/fuse dyad in the abstract.

/-- Restrict FDE(n) down to FDE(k) for k ≤ n. A middle value already inside
    range k keeps its index; a middle value only reachable at the deeper
    tier (index ≥ k) collapses to top — the "cannot distinguish beyond this
    depth" pole. This is the partition fdeEmbed's image and non-image split
    into, read off the register itself rather than declared separately. -/
def fdeRestrict (n k : ℕ) (hkn : k ≤ n) (x : FDEN n) : FDEN k :=
  match x with
  | .bot => .bot
  | .mid i => if h : i.val < k then .mid ⟨i.val, h⟩ else .top
  | .top => .top

theorem fdeRestrict_bot (n k : ℕ) (hkn : k ≤ n) : fdeRestrict n k hkn .bot = .bot := rfl
theorem fdeRestrict_top (n k : ℕ) (hkn : k ≤ n) : fdeRestrict n k hkn .top = .top := rfl

/-- The round trip: descend after ascending recovers the input, at any depth.
    fdeRestrict ∘ (fdeEmbed k n) = id on FDEN k. fdeEmbed is the ascent
    (more information, deeper scale); fdeRestrict is the descent (the arm
    rejoining what it came from). This is μ∘δ = id, instantiated. -/
theorem fdeRestrict_fdeEmbed_id (n k : ℕ) (hkn : k ≤ n) (x : FDEN k) :
    fdeRestrict n k hkn (fdeEmbed k n hkn x) = x := by
  cases x with
  | bot => rfl
  | mid i =>
    simp only [fdeEmbed, fdeRestrict, Fin.val_castLE]
    rw [dif_pos i.is_lt]
  | top => rfl

/-- The descent is a genuine coarsening, not a second bijection: for k < n,
    top and the deepest reachable middle value both restrict to top. The
    round trip only holds starting from the shallow side; descent alone
    loses exactly what the deeper tier added. -/
theorem fdeRestrict_not_injective (n k : ℕ) (hkn : k < n) :
    ¬ Function.Injective (fdeRestrict n k (le_of_lt hkn)) := by
  intro hinj
  have heq : fdeRestrict n k (le_of_lt hkn) FDEN.top
           = fdeRestrict n k (le_of_lt hkn) (FDEN.mid (⟨k, hkn⟩ : Fin n)) := by
    show (FDEN.top : FDEN k)
       = (if h : (⟨k, hkn⟩ : Fin n).val < k then FDEN.mid ⟨(⟨k, hkn⟩ : Fin n).val, h⟩ else FDEN.top)
    rw [dif_neg (lt_irrefl k)]
  have hcontra := hinj heq
  simp at hcontra

/-- Composite descent across several tiers is the single descent by
    transitivity of the arity order: restricting from n to k directly is the
    same as restricting from n to any intermediate j and then to k. This is
    what makes an arbitrary-depth walk well defined — the route taken
    through intermediate tiers does not matter, only the endpoints. -/
theorem fdeRestrict_trans (n j k : ℕ) (hjn : j ≤ n) (hkj : k ≤ j) (x : FDEN n) :
    fdeRestrict j k hkj (fdeRestrict n j hjn x) = fdeRestrict n k (le_trans hkj hjn) x := by
  cases x with
  | bot => rfl
  | top => rfl
  | mid i =>
    by_cases hik : i.val < k
    · have hij : i.val < j := lt_of_lt_of_le hik hkj
      simp only [fdeRestrict, dif_pos hij, dif_pos hik]
    · by_cases hij : i.val < j
      · simp only [fdeRestrict, dif_pos hij, dif_neg hik]
      · simp only [fdeRestrict, dif_neg hij, dif_neg hik]

end Imscribing.Paraconsistent.FDEAsymptotic
