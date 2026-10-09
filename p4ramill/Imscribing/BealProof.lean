-- This module serves as the root of the `BealProof` library.
-- The self-contained BealProof lake project lives at Imscribing/BealProof/
-- (own lakefile, own toolchain). This root reconnects the main Imscribing
-- build to the live Beal module that the lakefile globs actually carry.
import Imscribing.Millennium.Beal

namespace Imscribing.BealProof

-- The Beal Conjecture's structural encoding (Omega_0 status, sharpness at
-- exponent 2, promotion signature) lives in Imscribing.Millennium.Beal.
-- Reconnection witness: this namespace exists precisely because the import
-- above resolves against the main build's module path.
def main : IO Unit :=
  IO.println "BealProof root reconnected: import resolves to Imscribing.Millennium.Beal.\n"

end Imscribing.BealProof
