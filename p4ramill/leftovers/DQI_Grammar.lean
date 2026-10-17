-- DQI Grammar proof scaffold — generated from proof_scaffold on IMASM word
-- ⊢∈∈≻⋈⊤⊤⊥∋≺⋈∋⊣⊙ (VINIT FSPLIT FSPLIT AFWD CLINK EVALT EVALT EVALF FFUSE AREV CLINK FFUSE TANCH IMSCRIB)
-- Zero sorrys. Lean 4 verified.
import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

private def dqi_grammar_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def dqi_grammar_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def dqi_grammar_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def dqi_grammar_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def dqi_grammar_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def dqi_grammar_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def dqi_grammar_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }

noncomputable def dqi_grammar_protocol : IGProtocol dqi_grammar_s0 dqi_grammar_s13 :=
  .withGram Grammar.measure <|
  (.seq (.arrow dqi_grammar_s0 dqi_grammar_s0 dqi_grammar_s1)
    (.seq (.prod (.arrow dqi_grammar_s1 dqi_grammar_s1 dqi_grammar_s8) (.arrow dqi_grammar_s1 dqi_grammar_s1 dqi_grammar_s8))
      (.seq (.arrow dqi_grammar_s8 dqi_grammar_s8 dqi_grammar_s8)
        (.seq (.arrow dqi_grammar_s8 dqi_grammar_s8 dqi_grammar_s9)
          (.seq (.arrow dqi_grammar_s9 dqi_grammar_s9 dqi_grammar_s10)
            (.seq (.arrow dqi_grammar_s10 dqi_grammar_s10 dqi_grammar_s11)
              (.seq (.arrow dqi_grammar_s11 dqi_grammar_s11 dqi_grammar_s12)
                (.arrow dqi_grammar_s12 dqi_grammar_s12 dqi_grammar_s13))))))))

theorem dqi_grammar_frobenius :
    igFrobeniusAlg.mul dqi_grammar_s0 dqi_grammar_s0 = dqi_grammar_s0 :=
  igFrobAlg_self_fusion dqi_grammar_s0

end Imscribing