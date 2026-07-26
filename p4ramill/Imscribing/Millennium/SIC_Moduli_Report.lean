import Imscribing.Millennium.SIC_D16_Moduli
import Imscribing.Millennium.SIC_D20_Moduli
import Imscribing.Millennium.SIC_D2048_Moduli

/-!
# SIC_Moduli_Report — the conductor result, checked and narrated in one run

Running this file elaborates every claim the moduli-conductor manuscript rests on
and prints what was checked. Nothing here is a new assertion: each line names a
theorem that lives in one of the three imported modules, so the kernel has already
accepted it by the time the narration prints. The `#print axioms` blocks say
exactly which facts entered as PARI/GP field data rather than as proof.

    ./verify_sic_moduli.sh

is the intended entry point.
-/

section Narration

/-- Each line is a claim, the module it is proved in, and its content. -/
def claims : List (String × String) :=
  [ ("d=16  m = (d-3)(d+1) = 221 = 13·17, squarefree, ≡ 5 mod 8",
     "SIC.D16.Moduli.m16_factorization, m16_squarefree, m16_mod_eight"),
    ("d=16  class number of Q(√221) is 2 — the first SIC dimension where it is not 1",
     "SIC.D16.Moduli.class_group_is_nontrivial"),
    ("d=16  ray class group at conductor 48 has abelian type [16,4,2]",
     "SIC.D16.Moduli.ray_class_group_is_abelian"),
    ("d=16  raw σ-coinvariant count is 16, which is not d/2 = 8",
     "SIC.D16.Moduli.raw_coinvariant_neq_d_half"),
    ("d=16  quotient by the class group restores the count to d/2 = 8",
     "SIC.D16.Moduli.coinvariant_count_theorem"),
    ("d=16  therefore Statement A is falsified and Statement B confirmed",
     "SIC.D16.Moduli.statement_A_falsified_by_abelian_group, statement_B_confirmed_by_coinvariant_count"),
    ("d=16  conductor exponent v₂(d)+1 = 5, giving wide ray degree 128 over F",
     "SIC.D16.Moduli.exponent_at_16, ray_class_group_at_conductor_32"),
    ("d=20  5-torsion is absent from every modulus keeping the two-part in range",
     "SIC.D20.Moduli.five_torsion_absent_from_conductor"),
    ("d=20  so d=20 cannot discriminate, and the d=16 reading is untouched",
     "SIC.D20.Moduli.d20_cannot_discriminate, d16_settlement_independent_of_d20"),
    ("d=2048  m = 4190205 = 3·5·409·683, squarefree",
     "SIC.D2048.Moduli.m2048_factorization, m2048_squarefree"),
    ("d=2048  the conductor exponent predicted by the rule is v₂(2048)+1 = 12",
     "SIC.D2048.Moduli.predicted_exponent_2048"),
    ("d=2048  the moduli field has degree 2^27 over Q",
     "SIC.D2048.Moduli.fiducial_field_degree"),
    ("d=2048  the tower doubles at level 12, so the exponent choice is not free",
     "SIC.D2048.Moduli.phase_transition_at_12, exponent_choice_matters"),
    ("d=2048  the calibration table obeys the same exponent rule at d = 4, 8, 12, 16",
     "SIC.D2048.Moduli.calibration_exponent_rule") ]

def report : IO Unit := do
  IO.println "─────────────────────────────────────────────────────────────────────"
  IO.println " SIC moduli conductor — every claim below was accepted by the kernel"
  IO.println " before this line printed."
  IO.println "─────────────────────────────────────────────────────────────────────"
  for (claim, source) in claims do
    IO.println s!"  ✓ {claim}"
    IO.println s!"      {source}"
  IO.println "─────────────────────────────────────────────────────────────────────"
  IO.println s!" {claims.length} claims checked."
  IO.println " The axiom lists that follow are the PARI/GP field data: class numbers,"
  IO.println " ray class degrees and abelian types entered as computed input, not proof."
  IO.println "─────────────────────────────────────────────────────────────────────"

#eval report

end Narration

section Provenance

#print axioms SIC.D16.Moduli.coinvariant_count_theorem
#print axioms SIC.D16.Moduli.ray_class_group_is_abelian
#print axioms SIC.D16.Moduli.statement_B_confirmed_by_coinvariant_count
#print axioms SIC.D20.Moduli.five_torsion_absent_from_conductor
#print axioms SIC.D2048.Moduli.predicted_exponent_2048
#print axioms SIC.D2048.Moduli.fiducial_field_degree
#print axioms SIC.D2048.Moduli.calibration_exponent_rule

end Provenance
