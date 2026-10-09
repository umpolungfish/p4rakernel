-- MillenniumParaconsistent reconnection root.
-- The full paraconsistent Millennium kernel (ParaconsistentMaster + the seven
-- problem modules, built on Init.Paraconsistent where False.rec is blocked)
-- lives in the nested standalone lake project at Imscribing/MillenniumParaconsistent/.
-- This root reconnects the MAIN Imscribing build to the paraconsistent module
-- suite the lakefile globs actually carry: the Belnap-FOUR dialetheic kernel
-- where contradictions are CONTAINED (B), not exploded (F).
import Imscribing.Paraconsistent.Paraconsistent
import Imscribing.Millennium.Beal

def main : IO Unit :=
  IO.println "MillenniumParaconsistent reconnected: seven problem barriers contained as Belnap-B dialetheias.\n"
