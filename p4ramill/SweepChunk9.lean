import Imscribing.Ob3ects.tomographic_injection_scaffold
import Imscribing.Ob3ects.unproven_status_lacking_exact_frobenius_closure_scaffold
import Imscribing.Ob3ects.weyl_heisenberg_orbit_generation_for_the_d_12_br_scaffold
import Imscribing.Ob3ects.zauner_conjecture_bifurcation_splitting_general_scaffold
import Imscribing.Ob3ects.zauner_fiducial_scaffold
import Imscribing.ObjWitnessCosmos
import Imscribing.ObjWitnessVessel
import Imscribing.OddRingIndex
import Imscribing.Paraconsistent.B4Measurement
import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.BelnapAgreement
import Imscribing.Paraconsistent.BelnapCategory
import Imscribing.Paraconsistent.BelnapLL
import Imscribing.Paraconsistent.BelnapSplitFuse
import Imscribing.Paraconsistent.BelnapTemporal
import Imscribing.Paraconsistent.Betting
import Imscribing.Paraconsistent.BlackHoleBelnap
import Imscribing.Paraconsistent.ConsciousKernel
import Imscribing.Paraconsistent.CosmologyBelnap
import Imscribing.Paraconsistent.CrystalScheduler
import Imscribing.Paraconsistent.DialetheicAlignment
import Imscribing.Paraconsistent.ElectroweakBelnap
import Imscribing.Paraconsistent.ExoticHadronBelnap
import Imscribing.Paraconsistent.FDEAsymptotic
import Imscribing.Paraconsistent.FTLTravel
import Imscribing.Paraconsistent.FlavorMixing
import Imscribing.Paraconsistent.FrobeniusFiltration
import Imscribing.Paraconsistent.FrobeniusIso
import Imscribing.Paraconsistent.GaugeBosonBelnap
import Imscribing.Paraconsistent.GeneralRelativity
import Imscribing.Paraconsistent.GravitationalWaves
import Imscribing.Paraconsistent.GravityStandardModel
import Imscribing.Paraconsistent.HadronBelnap
import Imscribing.Paraconsistent.HiggsMechanism
import Imscribing.Paraconsistent.Init
import Imscribing.Paraconsistent.Kernel
import Imscribing.Paraconsistent.LeptonBelnap
import Imscribing.Paraconsistent.Main
import Imscribing.Paraconsistent.MajoranaFixed
import Imscribing.Paraconsistent.MultiAgentBelnap
import Imscribing.Vox.ProofLift
/-!
Sweep: lift every theorem THIS repo declares and emit `name<TAB>word<TAB>axioms`
for Vox to verdict in bulk. The lifter is NOT restated here — it lives once, in
`Imscribing.Vox.ProofLift`. Every copy of it that stood in these files was a
generation behind: `isSorry` matched the spelling rather than the axiom, and
`isAssumed` did not exist at all, so a declared axiom lifted to ◻ and read as
proved.
-/
#eval ProofLift.sweepAll
