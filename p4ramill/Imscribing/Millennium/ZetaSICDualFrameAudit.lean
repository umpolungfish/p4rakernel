import Imscribing.Millennium.ZetaSICDualFrame

open Imscribing.Millennium.ZetaSICDualFrame

#print axioms zeta_neg_one
#print axioms tetra_dual_left_inverse
#print axioms tetra_dual_right_inverse
#print axioms tetra_coordinate_reconstruction
#print axioms analytic_dual_frame_witness
#print axioms twelve_dual_left_inverse
#print axioms twelve_coordinate_reconstruction
#print axioms stranded_frame_weight
#print axioms final_fuse_recovers_four
#print axioms enclosing_repair_preserves_total

#eval sourceWord
#eval strandedWord
#eval (List.finRange 4).map exposedCheckpoint.reg
#eval (List.finRange 4).map strandedState.reg
#eval strandedState.frames.head?.map (fun f => (List.finRange 4).map f)
#eval (List.finRange 4).map strandedState.fuse.reg
#eval (List.finRange 4).map enclosingRepair.reg
