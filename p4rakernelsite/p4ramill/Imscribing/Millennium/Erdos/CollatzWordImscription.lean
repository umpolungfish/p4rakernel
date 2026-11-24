-- Imscribing/Millennium/Erdos/CollatzWordImscription.lean
--
-- The Collatz protocol words carry chirality `wool` with kinetics `yea`, and the
-- decomposition predicate refuses that pair.  Stated where it belongs -- on the
-- two slots the predicate actually reads -- so it covers every word carrying the
-- pair rather than one tuple.
--
--   depth split      ⊙∈≻≻∋⊡        ⟨𐑛𐑶𐑾𐑹𐑞𐑘𐑔𐑠𐑣𐑫𐑳𐑭⟩  crystal  3429838
--   mod-9 rung   ⊢⊙∈⊞⊤⊥≺∋⋈⊡⊣  ⟨𐑛𐑶𐑾𐑹𐑐𐑘𐑲𐑠𐑻𐑫𐑳𐑭⟩  crystal  3444190
--
-- 𐑫 is wool (chirality, infinite memory) and 𐑘 is yea (kinetics), by the catalog's
-- glyph table.  The two words differ in four slots and agree on these two.

import Imscribing.Decomposition

namespace Imscribing.Decomposition

open Imscribing.Primitives

/-- `wool` with `yea` is refused: infinite memory demands `egg` or `on`, and `yea`
    is neither.  The predicate reads chirality and kinetics only, so this covers
    every imscription carrying the pair, whatever its other ten slots hold. -/
theorem wool_yea_refused (s : Imscription) (hc : s.chir = .wool) (hk : s.kin = .yea) :
    ¬ InfiniteMemoryNeedsSlowKinetics s := by
  intro hp
  rcases hp hc with h | h <;> rw [hk] at h <;> exact absurd h (by decide)

/-- And the pair is the whole of it: with `wool`, the predicate holds exactly when
    the kinetics is `egg` or `on`. -/
theorem wool_iff (s : Imscription) (hc : s.chir = .wool) :
    InfiniteMemoryNeedsSlowKinetics s ↔ (s.kin = .egg ∨ s.kin = .on) := by
  constructor
  · intro hp; exact hp hc
  · intro h _; exact h

end Imscribing.Decomposition
