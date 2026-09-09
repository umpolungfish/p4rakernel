import Imscribing.ABC_SmallCertificate
import Imscribing.ABC_Window32_E1_10
import Imscribing.ABC_ScaleClosure
import Imscribing.ABC_ScaleChain
import Imscribing.ABC_AsymptoticClosure
import Imscribing.ABC_TailRegime
import Imscribing.ABC_IUTTClosure
import Imscribing.ABC_IUTTAsymptotic
import Imscribing.ABC_Measurement
import Imscribing.ABC_MeasurementChain
import Imscribing.ABC_MeasurementCompatibility
import Imscribing.ABC_MeasurementStream
import Imscribing.ABC_Champions
import Imscribing.ABC_ChampionTraceNine
import Imscribing.ABC_Window70_FromOS

/-! Axiom audit of arithmetic, quality, and Witness declarations. -/

#print axioms Imscribing.ABC.radical_eq_primeFactors
#print axioms Imscribing.ABC.radical_pos
#print axioms Imscribing.ABC.radical_one
#print axioms Imscribing.ABC.radical_prime
#print axioms Imscribing.ABC.radical_power
#print axioms Imscribing.ABC.Triple.c_pos
#print axioms Imscribing.ABC.Triple.pairwise_coprime
#print axioms Imscribing.ABC.rad_pos
#print axioms Imscribing.ABC.conjecture_iff_standard
#print axioms Imscribing.ABC.bound_iff_log_bound
#print axioms Imscribing.ABC.conjecture_iff_log_estimate
#print axioms Imscribing.ABC.log_estimate_iff_discrepancy
#print axioms Imscribing.ABC.conjecture_iff_uniform_discrepancy
#print axioms Imscribing.ABC.record_preserves_full_state
#print axioms Imscribing.ABC.packet_radical_calibration
#print axioms Imscribing.ABC.packet_height_calibration
#print axioms Imscribing.ABC.filtered_estimate_iff_log_estimate
#print axioms Imscribing.ABC.abc_of_filtered_estimate
#print axioms Imscribing.ABC.abc_of_calibrated_filtered_bound
#print axioms Imscribing.ABC.radical_216
#print axioms Imscribing.ABC.example_radical
#print axioms Imscribing.ABC.naive_radical_bound_fails
#print axioms Imscribing.ABC.rad_ge_two
#print axioms Imscribing.ABC.logRadical_ge_log_two
#print axioms Imscribing.ABC.logRadical_pos
#print axioms Imscribing.ABC.quality_bounded_of_log_estimate
#print axioms Imscribing.ABC.primeSupportWitness_is_B
#print axioms Imscribing.ABC.filteredRepresentationWitness_is_B
#print axioms Imscribing.ABC.arithmeticClosure_is_B
#print axioms Imscribing.ABC.primeSupportClass_is_B
#print axioms Imscribing.ABC.abcVerdict_is_B
#print axioms Imscribing.ABC.abc_of_verdict
#print axioms Imscribing.ABC.abc_from_filtered_via_verdict
#print axioms Imscribing.ABC.verdict_extraction_tracks_positive
#print axioms Imscribing.ABC.abc_of_held_verdict
#print axioms Imscribing.ABC.quality_bounded_of_held_verdict
#print axioms Imscribing.ABC.quality_bound_or_nonpositive
#print axioms Imscribing.ABC.abc_from_held_witness
#print axioms Imscribing.ABC.primeSupportWitness
#print axioms Imscribing.ABC.filteredRepresentationWitness
#print axioms Imscribing.ABC.arithmeticClosure
#print axioms Imscribing.ABC.abcVerdict
#print axioms Imscribing.ABC.abc_of_verdict_refined
#print axioms Imscribing.ABC.iutt_abc_dialetheia

#print axioms Imscribing.ABC.RoundTrip.outward_injective
#print axioms Imscribing.ABC.RoundTrip.observable_returns
#print axioms Imscribing.ABC.every_observable_has_round_trip
#print axioms Imscribing.ABC.abc_of_round_trip_bound
#print axioms Imscribing.ABC.SublinearComparisonError.add
#print axioms Imscribing.ABC.filtered_estimate_of_comparison
#print axioms Imscribing.ABC.comparisonClosure
#print axioms Imscribing.ABC.comparisonClosure_is_B

#print axioms Imscribing.ABC.reconstruct_factorization
#print axioms Imscribing.ABC.primePresentation_recovers
#print axioms Imscribing.ABC.primePresentation_injective
#print axioms Imscribing.ABC.primeHeight_calibration
#print axioms Imscribing.ABC.primeSupportHeight_calibration
#print axioms Imscribing.ABC.primeExcess_calibration
#print axioms Imscribing.ABC.prime_height_comparison
#print axioms Imscribing.ABC.prime_support_uniform_bound
#print axioms Imscribing.ABC.primeExcess_sublinear_iff_abc
#print axioms Imscribing.ABC.height_le_rad_of_squarefree
#print axioms Imscribing.ABC.primeExcess_nonpos_of_squarefree
#print axioms Imscribing.ABC.squarefree_discrepancy_bound
#print axioms Imscribing.ABC.squarefree_abc_bound
#print axioms Imscribing.ABC.squarefreeArithmeticWitness
#print axioms Imscribing.ABC.squarefreeArithmeticWitness_is_B
#print axioms Imscribing.ABC.abc_iff_nonsquarefree_discrepancy

#print axioms Imscribing.ABC.discrepancyOperator_action
#print axioms Imscribing.ABC.arithmeticEigenvalue_iff
#print axioms Imscribing.ABC.finite_spectrum_has_maximum
#print axioms Imscribing.ABC.uniform_spectral_iff_abc
#print axioms Imscribing.ABC.squarefree_spectrum_nonpositive
#print axioms Imscribing.ABC.spectralClosure
#print axioms Imscribing.ABC.spectralClosure_is_B

#print axioms Imscribing.ABC.pairTriple_height
#print axioms Imscribing.ABC.mem_arithmeticWindow
#print axioms Imscribing.ABC.arithmeticWindow_nonempty
#print axioms Imscribing.ABC.arithmeticWindow_monotone
#print axioms Imscribing.ABC.arithmeticWindow_exhaustive
#print axioms Imscribing.ABC.discrepancy_le_windowMaximum
#print axioms Imscribing.ABC.windowMaximum_le
#print axioms Imscribing.ABC.windowMaximum_monotone
#print axioms Imscribing.ABC.windowMaximum_attained
#print axioms Imscribing.ABC.windowFamily_mem
#print axioms Imscribing.ABC.windowMaximum_is_largest_eigenvalue
#print axioms Imscribing.ABC.window_bounded_iff_discrepancy
#print axioms Imscribing.ABC.window_converges_iff_bounded
#print axioms Imscribing.ABC.abc_iff_window_convergence

#print axioms Imscribing.ABC.WindowEnclosure.bounds_sample
#print axioms Imscribing.ABC.TailCertificate.uniform_bound
#print axioms Imscribing.ABC.discrepancy_antitone
#print axioms Imscribing.ABC.windowMaximum_antitone
#print axioms Imscribing.ABC.abc_iff_reciprocal_bounds
#print axioms Imscribing.ABC.abc_of_reciprocal_tail_certificates
#print axioms Imscribing.ABC.certifiedSpectralClosure
#print axioms Imscribing.ABC.certifiedSpectralClosure_is_B

#print axioms Imscribing.ABC.log_series_enclosure
#print axioms Imscribing.ABC.log_binary_enclosure
#print axioms Imscribing.ABC.discrepancy_enclosure
#print axioms Imscribing.ABC.certified_window_nine_upper
#print axioms Imscribing.ABC.certified_window_nine_lower
#print axioms Imscribing.ABC.certifiedWindowNine
#print axioms Imscribing.ABC.certifiedWindowNineWitness
#print axioms Imscribing.ABC.certifiedWindowNineWitness_is_B

#print axioms Imscribing.ABC.discrepancy_swap
#print axioms Imscribing.ABC.window_upper_of_ordered
#print axioms Imscribing.ABC.Window32E1_10.certified_upper
#print axioms Imscribing.ABC.Window32E1_10.certified_lower
#print axioms Imscribing.ABC.Window32E1_10.enclosure
#print axioms Imscribing.ABC.Window32E1_10.witness
#print axioms Imscribing.ABC.Window32E1_10.witness_is_B
#print axioms Imscribing.ABC.scaleLink_of_le
#print axioms Imscribing.ABC.enclosure_cross_bound
#print axioms Imscribing.ABC.enclosure_lower_monotone
#print axioms Imscribing.ABC.scaleClosureWitness
#print axioms Imscribing.ABC.scaleClosureWitness_is_B
#print axioms Imscribing.ABC.certifiedNineToThirty
#print axioms Imscribing.ABC.certifiedNineToThirty_cross
#print axioms Imscribing.ABC.certifiedNineToThirtyWitness
#print axioms Imscribing.ABC.certifiedNineToThirtyWitness_is_B
#print axioms Imscribing.ABC.scaleLink_trans
#print axioms Imscribing.ABC.ScaleChain.link
#print axioms Imscribing.ABC.ScaleChain.cross_bound
#print axioms Imscribing.ABC.ScaleChain.lower_or_cross
#print axioms Imscribing.ABC.certifiedTwoScale
#print axioms Imscribing.ABC.certifiedTwoScale_cross
#print axioms Imscribing.ABC.certifiedTwoScaleWitness
#print axioms Imscribing.ABC.certifiedTwoScaleWitness_is_B
#print axioms Imscribing.ABC.AsymptoticClosure.bounded
#print axioms Imscribing.ABC.AsymptoticClosure.maximum_le_limit
#print axioms Imscribing.ABC.AsymptoticClosure.to_conjecture
#print axioms Imscribing.ABC.asymptoticWitness
#print axioms Imscribing.ABC.asymptoticWitness_is_B
#print axioms Imscribing.ABC.chain_reading_below_asymptotic
#print axioms Imscribing.ABC.asymptotic_lower_contains_finite
#print axioms Imscribing.ABC.exactTailRegime
#print axioms Imscribing.ABC.TailRegime.read_monotone
#print axioms Imscribing.ABC.TailRegime.read_attained
#print axioms Imscribing.ABC.TailRegime.read_dominates
#print axioms Imscribing.ABC.tailClosureWitness
#print axioms Imscribing.ABC.tailClosureWitness_is_B
#print axioms Imscribing.ABC.tailClosure_preserves_finite_reading
#print axioms Imscribing.ABC.tailClosure_preserves_triple
#print axioms Imscribing.ABC.IUTTTailReading.select
#print axioms Imscribing.ABC.IUTTTailReading.packet_radical
#print axioms Imscribing.ABC.IUTTTailReading.packet_height
#print axioms Imscribing.ABC.exactIUTTTailClosure
#print axioms Imscribing.ABC.exactIUTTTailClosure_readout
#print axioms Imscribing.ABC.iuttTailClosureWitness
#print axioms Imscribing.ABC.iuttTailClosureWitness_is_B
#print axioms Imscribing.ABC.IUTTAsymptoticReading.read_is_window
#print axioms Imscribing.ABC.IUTTAsymptoticReading.toClosure
#print axioms Imscribing.ABC.IUTTAsymptoticReading.maximum_le_limit
#print axioms Imscribing.ABC.IUTTAsymptoticReading.triple_below_limit
#print axioms Imscribing.ABC.iutt_asymptotic_to_conjecture
#print axioms Imscribing.ABC.iuttAsymptoticWitness
#print axioms Imscribing.ABC.iuttAsymptoticWitness_is_B
#print axioms Imscribing.ABC.IUTTAsymptoticReading.ofWindowConvergence
#print axioms Imscribing.ABC.iuttAsymptoticFamilyOfConvergence
#print axioms Imscribing.ABC.iuttAsymptoticFamilyOfConvergence_to_conjecture
#print axioms Imscribing.ABC.iuttAsymptoticWitnessOfConvergence
#print axioms Imscribing.ABC.iuttAsymptoticWitnessOfConvergence_is_B
#print axioms Imscribing.ABC.FiniteMeasurement.ofEnclosure
#print axioms Imscribing.ABC.FiniteMeasurement.packet_height
#print axioms Imscribing.ABC.FiniteMeasurement.packet_radical
#print axioms Imscribing.ABC.FiniteMeasurement.readout
#print axioms Imscribing.ABC.FiniteMeasurement.witness
#print axioms Imscribing.ABC.FiniteMeasurement.witness_is_B
#print axioms Imscribing.ABC.certifiedMeasurementNine
#print axioms Imscribing.ABC.certifiedMeasurementThirty
#print axioms Imscribing.ABC.MeasurementChain.fromScaleChain
#print axioms Imscribing.ABC.MeasurementChain.link
#print axioms Imscribing.ABC.MeasurementChain.cross_bound
#print axioms Imscribing.ABC.MeasurementChain.witness
#print axioms Imscribing.ABC.MeasurementChain.witness_is_B
#print axioms Imscribing.ABC.certifiedMeasurementChain
#print axioms Imscribing.ABC.certifiedMeasurementChain_cross
#print axioms Imscribing.ABC.certifiedMeasurementChain_witness_is_B
#print axioms Imscribing.ABC.MeasurementChain.lower_le_limit
#print axioms Imscribing.ABC.MeasurementChain.triple_le_limit
#print axioms Imscribing.ABC.MeasurementChain.packet_calibrated
#print axioms Imscribing.ABC.MeasurementChain.compatibilityWitness
#print axioms Imscribing.ABC.MeasurementChain.compatibilityWitness_is_B
#print axioms Imscribing.ABC.CertifiedMeasurementStream.measurement_readout
#print axioms Imscribing.ABC.CertifiedMeasurementStream.prefix
#print axioms Imscribing.ABC.CertifiedMeasurementStream.prefix_cross_bound
#print axioms Imscribing.ABC.CertifiedMeasurementStream.witness
#print axioms Imscribing.ABC.CertifiedMeasurementStream.witness_is_B
#print axioms Imscribing.ABC.ChampionEvent.packet_calibrated
#print axioms Imscribing.ABC.certifiedChampionTraceNine
#print axioms Imscribing.ABC.champion_base_through_eight
#print axioms Imscribing.ABC.champion_at_nine
#print axioms Imscribing.ABC.displacement_through_nine_iff
#print axioms Imscribing.ABC.certifiedChampionTraceNineWitness
#print axioms Imscribing.ABC.certifiedChampionTraceNineWitness_is_B
#print axioms Imscribing.ABC.Window70E1_10.enclosure
#print axioms Imscribing.ABC.Window70E1_10.witness
#print axioms Imscribing.ABC.Window70E1_10.witness_is_B
