import Imscribing.Biochem.PrimaLogicaMechanicalGlut

/-!
# Mechanical-glut bridge audit (requires Mathlib + the Imscribing fork)

Run from the project root:

  lake build Imscribing.Biochem.PrimaLogicaMechanicalGlut
    Imscribing.Biochem.PrimaLogicaMechanicalGlutAudit

Do not infer verification from the presence of #check: the Lean kernel must
successfully compile the imported source to certify these declarations.
-/

open Imscribing.PrimaLogica.MechanicalGlut

#check mu_delta_id
#check mu_after_winding
#check separatedBoth_isBoth
#check MechanicalGlut.gradU_qStar
#check MechanicalGlut.U_decomposition
#check MechanicalGlut.epsilon_pos
#check MechanicalGlut.U_qStar_le
#check MechanicalGlut.Eg_pos
#check MechanicalGlut.Eg_le_epsilon
#check MechanicalGlut.productive_work
#check B_realizes_positive_energy
#check B_realizes_positive_bounded_work
#check after_winding_produces_bounded_work

#print axioms mu_delta_id
#print axioms MechanicalGlut.U_decomposition
#print axioms MechanicalGlut.epsilon_pos
#print axioms MechanicalGlut.Eg_pos
#print axioms MechanicalGlut.productive_work
#print axioms after_winding_produces_bounded_work

#check LatticeInteraction.fuse_response
#check LatticeInteraction.reconstruct_interactions
#check LatticeInteraction.interactions_reconstruct
#check LatticeInteraction.cooperative_pair_coefficient
#check LatticeInteraction.difference_derivative
#check LatticeInteraction.truth_response_balance
#check LatticeInteraction.falsity_response_balance
#check LatticeInteraction.disjoint_split_fuse
#check LatticeInteraction.PotentialFamily.energy_derivative
#check LatticeInteraction.PotentialFamily.force_fuse
#check LatticeInteraction.PotentialFamily.pair_forces
#check LatticeInteraction.mechanical_derivative
#check LatticeInteraction.mechanical_step_work
#check LatticeInteraction.mechanical_step_lowers_energy

#print axioms LatticeInteraction.fuse_response
#print axioms LatticeInteraction.reconstruct_interactions
#print axioms LatticeInteraction.PotentialFamily.energy_derivative
#print axioms LatticeInteraction.mechanical_step_lowers_energy

#check NativeGlut.encoding
#check NativeGlut.equilibrium
#check NativeGlut.retained_strain
#check NativeGlut.released_work
#print axioms NativeGlut.equilibrium
#print axioms NativeGlut.retained_strain
#print axioms NativeGlut.released_work
#check NativeFrame.vertex_gram
#check NativeFrame.tetrahedral_ratio
#check NativeFrame.face_gram
#check NativeFrame.planar_ratio
#print axioms NativeFrame.vertex_gram
#print axioms NativeFrame.planar_ratio

#check NativeSelection.contexts_bounded
#check NativeSelection.maximum_offered
#check NativeSelection.retain_information
#check NativeSelection.retain_idempotent
#print axioms NativeSelection.contexts_bounded
#print axioms NativeSelection.retain_information
