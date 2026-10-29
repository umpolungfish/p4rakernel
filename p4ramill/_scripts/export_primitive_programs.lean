import Imscribing.Primitives.Types.PrimitiveTypeAdo
import Imscribing.Primitives.Types.PrimitiveTypeAge
import Imscribing.Primitives.Types.PrimitiveTypeAh
import Imscribing.Primitives.Types.PrimitiveTypeAir
import Imscribing.Primitives.Types.PrimitiveTypeAre
import Imscribing.Primitives.Types.PrimitiveTypeArray
import Imscribing.Primitives.Types.PrimitiveTypeAsh
import Imscribing.Primitives.Types.PrimitiveTypeAwe
import Imscribing.Primitives.Types.PrimitiveTypeBib
import Imscribing.Primitives.Types.PrimitiveTypeChurch
import Imscribing.Primitives.Types.PrimitiveTypeDead
import Imscribing.Primitives.Types.PrimitiveTypeEar
import Imscribing.Primitives.Types.PrimitiveTypeEat
import Imscribing.Primitives.Types.PrimitiveTypeEgg
import Imscribing.Primitives.Types.PrimitiveTypeErr
import Imscribing.Primitives.Types.PrimitiveTypeFee
import Imscribing.Primitives.Types.PrimitiveTypeGag
import Imscribing.Primitives.Types.PrimitiveTypeHaHa
import Imscribing.Primitives.Types.PrimitiveTypeHung
import Imscribing.Primitives.Types.PrimitiveTypeIan
import Imscribing.Primitives.Types.PrimitiveTypeIce
import Imscribing.Primitives.Types.PrimitiveTypeIf
import Imscribing.Primitives.Types.PrimitiveTypeJudge
import Imscribing.Primitives.Types.PrimitiveTypeKick
import Imscribing.Primitives.Types.PrimitiveTypeLoll
import Imscribing.Primitives.Types.PrimitiveTypeMeasure
import Imscribing.Primitives.Types.PrimitiveTypeMime
import Imscribing.Primitives.Types.PrimitiveTypeMonad
import Imscribing.Primitives.Types.PrimitiveTypeNun
import Imscribing.Primitives.Types.PrimitiveTypeOak
import Imscribing.Primitives.Types.PrimitiveTypeOil
import Imscribing.Primitives.Types.PrimitiveTypeOn
import Imscribing.Primitives.Types.PrimitiveTypeOoze
import Imscribing.Primitives.Types.PrimitiveTypeOr
import Imscribing.Primitives.Types.PrimitiveTypeOut
import Imscribing.Primitives.Types.PrimitiveTypePeep
import Imscribing.Primitives.Types.PrimitiveTypeRoar
import Imscribing.Primitives.Types.PrimitiveTypeSo
import Imscribing.Primitives.Types.PrimitiveTypeSure
import Imscribing.Primitives.Types.PrimitiveTypeThey
import Imscribing.Primitives.Types.PrimitiveTypeThigh
import Imscribing.Primitives.Types.PrimitiveTypeTot
import Imscribing.Primitives.Types.PrimitiveTypeUp
import Imscribing.Primitives.Types.PrimitiveTypeVow
import Imscribing.Primitives.Types.PrimitiveTypeWoe
import Imscribing.Primitives.Types.PrimitiveTypeWool
import Imscribing.Primitives.Types.PrimitiveTypeYea
import Imscribing.Primitives.Types.PrimitiveTypeYew
import Imscribing.Primitives.Types.PrimitiveTypeZoo
import Lean

open Imscribing Imscribing.Primitives.Types Lean

def primitiveProgramRows : List (String × String × String × List String × List String × List (Nat × Nat)) := [
  ("ado", "Imscribing/Primitives/Types/PrimitiveTypeAdo.lean", the_primitive_type_called_ado_glyphWord, the_primitive_type_called_ado_opcodes, the_primitive_type_called_ado_domainActions, the_primitive_type_called_ado_forkFusePairs),
  ("age", "Imscribing/Primitives/Types/PrimitiveTypeAge.lean", the_primitive_type_called_age_glyphWord, the_primitive_type_called_age_opcodes, the_primitive_type_called_age_domainActions, the_primitive_type_called_age_forkFusePairs),
  ("ah", "Imscribing/Primitives/Types/PrimitiveTypeAh.lean", the_primitive_type_called_ah_glyphWord, the_primitive_type_called_ah_opcodes, the_primitive_type_called_ah_domainActions, the_primitive_type_called_ah_forkFusePairs),
  ("air", "Imscribing/Primitives/Types/PrimitiveTypeAir.lean", the_primitive_type_called_air_glyphWord, the_primitive_type_called_air_opcodes, the_primitive_type_called_air_domainActions, the_primitive_type_called_air_forkFusePairs),
  ("are", "Imscribing/Primitives/Types/PrimitiveTypeAre.lean", the_primitive_type_called_are_glyphWord, the_primitive_type_called_are_opcodes, the_primitive_type_called_are_domainActions, the_primitive_type_called_are_forkFusePairs),
  ("array", "Imscribing/Primitives/Types/PrimitiveTypeArray.lean", the_primitive_type_called_array_glyphWord, the_primitive_type_called_array_opcodes, the_primitive_type_called_array_domainActions, the_primitive_type_called_array_forkFusePairs),
  ("ash", "Imscribing/Primitives/Types/PrimitiveTypeAsh.lean", the_primitive_type_called_ash_glyphWord, the_primitive_type_called_ash_opcodes, the_primitive_type_called_ash_domainActions, the_primitive_type_called_ash_forkFusePairs),
  ("awe", "Imscribing/Primitives/Types/PrimitiveTypeAwe.lean", the_primitive_type_called_awe_glyphWord, the_primitive_type_called_awe_opcodes, the_primitive_type_called_awe_domainActions, the_primitive_type_called_awe_forkFusePairs),
  ("bib", "Imscribing/Primitives/Types/PrimitiveTypeBib.lean", the_primitive_type_called_bib_glyphWord, the_primitive_type_called_bib_opcodes, the_primitive_type_called_bib_domainActions, the_primitive_type_called_bib_forkFusePairs),
  ("church", "Imscribing/Primitives/Types/PrimitiveTypeChurch.lean", the_primitive_type_called_church_glyphWord, the_primitive_type_called_church_opcodes, the_primitive_type_called_church_domainActions, the_primitive_type_called_church_forkFusePairs),
  ("dead", "Imscribing/Primitives/Types/PrimitiveTypeDead.lean", the_primitive_type_called_dead_glyphWord, the_primitive_type_called_dead_opcodes, the_primitive_type_called_dead_domainActions, the_primitive_type_called_dead_forkFusePairs),
  ("ear", "Imscribing/Primitives/Types/PrimitiveTypeEar.lean", the_primitive_type_called_ear_glyphWord, the_primitive_type_called_ear_opcodes, the_primitive_type_called_ear_domainActions, the_primitive_type_called_ear_forkFusePairs),
  ("eat", "Imscribing/Primitives/Types/PrimitiveTypeEat.lean", the_primitive_type_called_eat_glyphWord, the_primitive_type_called_eat_opcodes, the_primitive_type_called_eat_domainActions, the_primitive_type_called_eat_forkFusePairs),
  ("egg", "Imscribing/Primitives/Types/PrimitiveTypeEgg.lean", the_primitive_type_called_egg_glyphWord, the_primitive_type_called_egg_opcodes, the_primitive_type_called_egg_domainActions, the_primitive_type_called_egg_forkFusePairs),
  ("err", "Imscribing/Primitives/Types/PrimitiveTypeErr.lean", the_primitive_type_called_err_glyphWord, the_primitive_type_called_err_opcodes, the_primitive_type_called_err_domainActions, the_primitive_type_called_err_forkFusePairs),
  ("fee", "Imscribing/Primitives/Types/PrimitiveTypeFee.lean", the_primitive_type_called_fee_glyphWord, the_primitive_type_called_fee_opcodes, the_primitive_type_called_fee_domainActions, the_primitive_type_called_fee_forkFusePairs),
  ("gag", "Imscribing/Primitives/Types/PrimitiveTypeGag.lean", the_primitive_type_called_gag_glyphWord, the_primitive_type_called_gag_opcodes, the_primitive_type_called_gag_domainActions, the_primitive_type_called_gag_forkFusePairs),
  ("ha_ha", "Imscribing/Primitives/Types/PrimitiveTypeHaHa.lean", the_primitive_type_called_ha_ha_glyphWord, the_primitive_type_called_ha_ha_opcodes, the_primitive_type_called_ha_ha_domainActions, the_primitive_type_called_ha_ha_forkFusePairs),
  ("hung", "Imscribing/Primitives/Types/PrimitiveTypeHung.lean", the_primitive_type_called_hung_glyphWord, the_primitive_type_called_hung_opcodes, the_primitive_type_called_hung_domainActions, the_primitive_type_called_hung_forkFusePairs),
  ("ian", "Imscribing/Primitives/Types/PrimitiveTypeIan.lean", the_primitive_type_called_ian_glyphWord, the_primitive_type_called_ian_opcodes, the_primitive_type_called_ian_domainActions, the_primitive_type_called_ian_forkFusePairs),
  ("ice", "Imscribing/Primitives/Types/PrimitiveTypeIce.lean", the_primitive_type_called_ice_glyphWord, the_primitive_type_called_ice_opcodes, the_primitive_type_called_ice_domainActions, the_primitive_type_called_ice_forkFusePairs),
  ("if", "Imscribing/Primitives/Types/PrimitiveTypeIf.lean", the_primitive_type_called_if_glyphWord, the_primitive_type_called_if_opcodes, the_primitive_type_called_if_domainActions, the_primitive_type_called_if_forkFusePairs),
  ("judge", "Imscribing/Primitives/Types/PrimitiveTypeJudge.lean", the_primitive_type_called_judge_glyphWord, the_primitive_type_called_judge_opcodes, the_primitive_type_called_judge_domainActions, the_primitive_type_called_judge_forkFusePairs),
  ("kick", "Imscribing/Primitives/Types/PrimitiveTypeKick.lean", the_primitive_type_called_kick_glyphWord, the_primitive_type_called_kick_opcodes, the_primitive_type_called_kick_domainActions, the_primitive_type_called_kick_forkFusePairs),
  ("loll", "Imscribing/Primitives/Types/PrimitiveTypeLoll.lean", the_primitive_type_called_loll_glyphWord, the_primitive_type_called_loll_opcodes, the_primitive_type_called_loll_domainActions, the_primitive_type_called_loll_forkFusePairs),
  ("measure", "Imscribing/Primitives/Types/PrimitiveTypeMeasure.lean", the_primitive_type_called_measure_glyphWord, the_primitive_type_called_measure_opcodes, the_primitive_type_called_measure_domainActions, the_primitive_type_called_measure_forkFusePairs),
  ("mime", "Imscribing/Primitives/Types/PrimitiveTypeMime.lean", the_primitive_type_called_mime_glyphWord, the_primitive_type_called_mime_opcodes, the_primitive_type_called_mime_domainActions, the_primitive_type_called_mime_forkFusePairs),
  ("monad", "Imscribing/Primitives/Types/PrimitiveTypeMonad.lean", the_primitive_type_called_monad_glyphWord, the_primitive_type_called_monad_opcodes, the_primitive_type_called_monad_domainActions, the_primitive_type_called_monad_forkFusePairs),
  ("nun", "Imscribing/Primitives/Types/PrimitiveTypeNun.lean", the_primitive_type_called_nun_glyphWord, the_primitive_type_called_nun_opcodes, the_primitive_type_called_nun_domainActions, the_primitive_type_called_nun_forkFusePairs),
  ("oak", "Imscribing/Primitives/Types/PrimitiveTypeOak.lean", the_primitive_type_called_oak_glyphWord, the_primitive_type_called_oak_opcodes, the_primitive_type_called_oak_domainActions, the_primitive_type_called_oak_forkFusePairs),
  ("oil", "Imscribing/Primitives/Types/PrimitiveTypeOil.lean", the_primitive_type_called_oil_glyphWord, the_primitive_type_called_oil_opcodes, the_primitive_type_called_oil_domainActions, the_primitive_type_called_oil_forkFusePairs),
  ("on", "Imscribing/Primitives/Types/PrimitiveTypeOn.lean", the_primitive_type_called_on_glyphWord, the_primitive_type_called_on_opcodes, the_primitive_type_called_on_domainActions, the_primitive_type_called_on_forkFusePairs),
  ("ooze", "Imscribing/Primitives/Types/PrimitiveTypeOoze.lean", the_primitive_type_called_ooze_glyphWord, the_primitive_type_called_ooze_opcodes, the_primitive_type_called_ooze_domainActions, the_primitive_type_called_ooze_forkFusePairs),
  ("or", "Imscribing/Primitives/Types/PrimitiveTypeOr.lean", the_primitive_type_called_or_glyphWord, the_primitive_type_called_or_opcodes, the_primitive_type_called_or_domainActions, the_primitive_type_called_or_forkFusePairs),
  ("out", "Imscribing/Primitives/Types/PrimitiveTypeOut.lean", Imscribing.Primitives.Types.the_primitive_type_called_out_glyphWord, Imscribing.Primitives.Types.the_primitive_type_called_out_opcodes, Imscribing.Primitives.Types.the_primitive_type_called_out_domainActions, Imscribing.Primitives.Types.the_primitive_type_called_out_forkFusePairs),
  ("peep", "Imscribing/Primitives/Types/PrimitiveTypePeep.lean", the_primitive_type_called_peep_glyphWord, the_primitive_type_called_peep_opcodes, the_primitive_type_called_peep_domainActions, the_primitive_type_called_peep_forkFusePairs),
  ("roar", "Imscribing/Primitives/Types/PrimitiveTypeRoar.lean", the_primitive_type_called_roar_glyphWord, the_primitive_type_called_roar_opcodes, the_primitive_type_called_roar_domainActions, the_primitive_type_called_roar_forkFusePairs),
  ("so", "Imscribing/Primitives/Types/PrimitiveTypeSo.lean", the_primitive_type_called_so_glyphWord, the_primitive_type_called_so_opcodes, the_primitive_type_called_so_domainActions, the_primitive_type_called_so_forkFusePairs),
  ("sure", "Imscribing/Primitives/Types/PrimitiveTypeSure.lean", the_primitive_type_called_sure_glyphWord, the_primitive_type_called_sure_opcodes, the_primitive_type_called_sure_domainActions, the_primitive_type_called_sure_forkFusePairs),
  ("they", "Imscribing/Primitives/Types/PrimitiveTypeThey.lean", the_primitive_type_called_they_glyphWord, the_primitive_type_called_they_opcodes, the_primitive_type_called_they_domainActions, the_primitive_type_called_they_forkFusePairs),
  ("thigh", "Imscribing/Primitives/Types/PrimitiveTypeThigh.lean", the_primitive_type_called_thigh_glyphWord, the_primitive_type_called_thigh_opcodes, the_primitive_type_called_thigh_domainActions, the_primitive_type_called_thigh_forkFusePairs),
  ("tot", "Imscribing/Primitives/Types/PrimitiveTypeTot.lean", the_primitive_type_called_tot_glyphWord, the_primitive_type_called_tot_opcodes, the_primitive_type_called_tot_domainActions, the_primitive_type_called_tot_forkFusePairs),
  ("up", "Imscribing/Primitives/Types/PrimitiveTypeUp.lean", the_primitive_type_called_up_glyphWord, the_primitive_type_called_up_opcodes, the_primitive_type_called_up_domainActions, the_primitive_type_called_up_forkFusePairs),
  ("vow", "Imscribing/Primitives/Types/PrimitiveTypeVow.lean", the_primitive_type_called_vow_glyphWord, the_primitive_type_called_vow_opcodes, the_primitive_type_called_vow_domainActions, the_primitive_type_called_vow_forkFusePairs),
  ("woe", "Imscribing/Primitives/Types/PrimitiveTypeWoe.lean", the_primitive_type_called_woe_glyphWord, the_primitive_type_called_woe_opcodes, the_primitive_type_called_woe_domainActions, the_primitive_type_called_woe_forkFusePairs),
  ("wool", "Imscribing/Primitives/Types/PrimitiveTypeWool.lean", the_primitive_type_called_wool_glyphWord, the_primitive_type_called_wool_opcodes, the_primitive_type_called_wool_domainActions, the_primitive_type_called_wool_forkFusePairs),
  ("yea", "Imscribing/Primitives/Types/PrimitiveTypeYea.lean", the_primitive_type_called_yea_glyphWord, the_primitive_type_called_yea_opcodes, the_primitive_type_called_yea_domainActions, the_primitive_type_called_yea_forkFusePairs),
  ("yew", "Imscribing/Primitives/Types/PrimitiveTypeYew.lean", the_primitive_type_called_yew_glyphWord, the_primitive_type_called_yew_opcodes, the_primitive_type_called_yew_domainActions, the_primitive_type_called_yew_forkFusePairs),
  ("zoo", "Imscribing/Primitives/Types/PrimitiveTypeZoo.lean", the_primitive_type_called_zoo_glyphWord, the_primitive_type_called_zoo_opcodes, the_primitive_type_called_zoo_domainActions, the_primitive_type_called_zoo_forkFusePairs)
]

def main : IO Unit := do
  let programs := primitiveProgramRows.map fun (name, source, word, opcodes, actions, pairs) =>
    Json.mkObj [("name", toJson name), ("source", toJson source),
      ("word", toJson word), ("opcodes", toJson opcodes),
      ("actions", toJson actions), ("pairs", toJson pairs),
      ("dependencies", toJson (if name == "out" then
        ["Imscribing/Ob3ects/GateCheck/the_primitive_type_called_out_gate_check.lean"] else ([] : List String)))]
  IO.println (Json.mkObj [("schema", toJson (1 : Nat)), ("programs", toJson programs)]).compress
