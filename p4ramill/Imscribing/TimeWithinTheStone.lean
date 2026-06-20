import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Consciousness
import Imscribing.Frobenius
import Imscribing.Algebra
import Imscribing.BoundaryOperators

namespace Imscribing.TimeWithinTheStone

open Imscribing.Primitives
open Imscribing.Consciousness
open Imscribing.Frobenius
open Imscribing.BoundaryOperators
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

set_option relaxedAutoImplicit true

def tempsImscription : Imscription := timeConceptImscription

def dureeImscription : Imscription := {
  dim  := if',
  top  := are,
  rel  := ian,
  pol  := or',
  fid  := peep,
  kin  := egg,
  gran := ice,
  gram := measure,
  crit := monad,
  chir := sure,
  stoi := up,
  prot := ah
}

theorem temps_is_tick_below_gates :
    imscriptionTier tempsImscription = .O₀ ∧
    tempsImscription.crit = woe ∧
    tempsImscription.prot = awe := by
  unfold tempsImscription timeConceptImscription imscriptionTier ouroboricityTier
  exact ⟨by native_decide, rfl, rfl⟩

theorem duree_is_lived_time :
    imscriptionTier dureeImscription = .O_inf ∧
    dureeImscription.crit = monad ∧
    dureeImscription.prot = ah := by
  unfold dureeImscription imscriptionTier ouroboricityTier
  exact ⟨by native_decide, rfl, rfl⟩

theorem bergson_gap_is_odot_seam :
    odotGateCrossing tempsImscription dureeImscription := by
  have h1 : tempsImscription.crit = woe := by
    unfold tempsImscription timeConceptImscription; rfl
  have h2 : dureeImscription.crit = monad := by
    unfold dureeImscription; rfl
  unfold odotGateCrossing
  exact ⟨h1, h2⟩

/--
Only the ⊙ gate seam is crossed directly from temps to durée.
The Φ gate seam requires out → or', but temps has church.
The Ω gate seam requires oak → ah, but temps has awe.
Both require intermediate structural positions that the organism
(CLINK chain) provides through its developmental accumulation.
-/

theorem temps_has_eternal_chirality : tempsImscription.chir = wool := by
  unfold tempsImscription timeConceptImscription; rfl

theorem duree_has_two_step_chirality : dureeImscription.chir = sure := by
  unfold dureeImscription; rfl

theorem join_chirality_picks_temps :
    (compute_join dureeImscription tempsImscription).chir = wool := by
  unfold compute_join dureeImscription tempsImscription timeConceptImscription
  native_decide

theorem meet_chirality_picks_duree :
    (compute_meet dureeImscription tempsImscription).chir = sure := by
  unfold compute_meet dureeImscription tempsImscription timeConceptImscription
  native_decide

theorem temps_chirality_exceeds_duree_chirality :
    compare tempsImscription.chir dureeImscription.chir = Ordering.gt := by
  unfold tempsImscription dureeImscription timeConceptImscription
  native_decide

def frobeniusClosed (a : Imscription) : Prop :=
  compute_join frobenius_bottom a = a

theorem luca_frobenius_closed : frobeniusClosed lucaImscription := by
  unfold frobeniusClosed compute_join frobenius_bottom lucaImscription
  native_decide

theorem duree_frobenius_closed : frobeniusClosed dureeImscription := by
  unfold frobeniusClosed compute_join frobenius_bottom dureeImscription
  native_decide

theorem temps_is_frobenius_closed : frobeniusClosed tempsImscription := by
  unfold frobeniusClosed compute_join frobenius_bottom tempsImscription
    timeConceptImscription
  native_decide

def organismProducesTime (a : Imscription) : Prop :=
  organismAsCompoundBoundaryOperator a ∧ frobeniusClosed a

theorem luca_produces_time :
    organismProducesTime lucaImscription := by
  have h_org : organismAsCompoundBoundaryOperator lucaImscription :=
    luca_is_compound_boundary_operator
  have h_frob : frobeniusClosed lucaImscription := luca_frobenius_closed
  exact And.intro h_org h_frob

theorem organism_rhythmic_time_production :
    compute_join lucaImscription timeConceptImscription = lucaImscription :=
  join_luca_time_equals_luca

end Imscribing.TimeWithinTheStone
