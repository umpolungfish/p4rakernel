import Imscribing.Paraconsistent.TensorFiltration

open Imscribing.Paraconsistent.TensorFiltration

#print axioms native_theta
#print axioms theta_idempotent
#print axioms theta_fixed_count
#print axioms trace_does_not_factor_through_erasure
#print axioms phase_operator_trace
#print axioms carrier_operator_trace
#print axioms compiled_theta_trace
#print axioms audited_extracted_trace
#print axioms ladder_symmetric
#print axioms ladder_off_diagonal
#print axioms ladder_tridiagonal
#print axioms raised_weight_square

#eval phaseSum
#eval traceProgram.length
#eval audit traceProgram
#eval (execute traceProgram (theta Imscribing.IUTT.empty)).accumulator
#eval (execute traceProgram (Imscribing.IUTT.eraseInformation
  (theta Imscribing.IUTT.empty))).accumulator
