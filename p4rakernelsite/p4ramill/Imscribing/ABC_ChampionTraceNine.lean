import Imscribing.ABC_Champions
import Imscribing.ABC_ChampionNineBounds

namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

/-- No displacement at any height cutoff from 2 through 8. -/
theorem champion_base_through_eight (N : ℕ) (hN : N ≤ 6) :
    windowMaximum (1/10) N = discrepancy (1/10) baseTriple := by
  apply le_antisymm
  · apply windowMaximum_le
    intro t ht
    apply ChampionNineBounds.upper_8
    have := (mem_arithmeticWindow N t).mp ht
    omega
  · exact discrepancy_le_windowMaximum _ _ _
      ((mem_arithmeticWindow N baseTriple).mpr (by simp [baseTriple]))

theorem champion_at_nine :
    discrepancy (1/10) one_eight_nine = windowMaximum (1/10) 7 := by
  apply le_antisymm
  · exact discrepancy_le_windowMaximum _ _ _
      ((mem_arithmeticWindow 7 one_eight_nine).mpr (by decide))
  · exact windowMaximum_le _ _ _ (fun t ht =>
      ChampionNineBounds.upper_9 t ((mem_arithmeticWindow 7 t).mp ht))

def championInitial : ChampionEvent (1/10) where
  cutoff := 0
  previous := none
  champion := baseTriple
  member := (mem_arithmeticWindow 0 baseTriple).mpr (by decide)
  reading := (champion_base_through_eight 0 (by omega)).symm
  displaces := by simp
  previous_reading := by simp

def championAtNine : ChampionEvent (1/10) where
  cutoff := 7
  previous := some baseTriple
  champion := one_eight_nine
  member := (mem_arithmeticWindow 7 one_eight_nine).mpr (by decide)
  reading := champion_at_nine
  displaces := by
    intro p hp
    cases Option.some.inj hp
    exact ChampionNineBounds.strict_displacement
  previous_reading := by
    intro p hp
    cases Option.some.inj hp
    exact ⟨by decide, (champion_base_through_eight 6 (by omega)).symm⟩

def certifiedChampionTraceNine : ChampionTrace (1/10) where
  events := [championInitial, championAtNine]
  ordered := by simp [championInitial, championAtNine]
  initial := by
    intro e he
    simp only [List.head?_cons, Option.some.injEq] at he
    subst e
    exact ⟨rfl, rfl⟩
  linked := by
    intro i e f he hf
    have hi : i < 2 := by
      by_contra h
      have hn : 2 ≤ i := by omega
      have hz : [championInitial, championAtNine][i]? = none :=
        List.getElem?_eq_none (by simpa using hn)
      rw [hz] at he
      contradiction
    interval_cases i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      simp at hf
      subst e; subst f
      rfl
    · simp at hf
  stable_between := by
    intro i e f he hf N hlo hhi
    have hi : i < 2 := by
      by_contra h
      have hn : 2 ≤ i := by omega
      have hz : [championInitial, championAtNine][i]? = none :=
        List.getElem?_eq_none (by simpa using hn)
      rw [hz] at he
      contradiction
    interval_cases i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      simp at hf
      subst e; subst f
      exact champion_base_through_eight N (by change N < 7 at hhi; omega)
    · simp at hf

/-- Complete list of strict maximum displacements through height cutoff 9. -/
theorem displacement_through_nine_iff (N : ℕ) (hN : N ≤ 7) :
    DisplacementAt (1/10) N ↔ N = 7 := by
  constructor
  · rintro ⟨hpos, hstrict⟩
    by_contra hne
    have hsmall : N ≤ 6 := by omega
    rw [champion_base_through_eight N hsmall,
      champion_base_through_eight (N-1) (by omega)] at hstrict
    exact (lt_irrefl _ hstrict)
  · rintro rfl
    exact championAtNine.displacement baseTriple rfl

theorem certifiedChampionTraceNine_height_cutoffs :
    certifiedChampionTraceNine.events.map ChampionEvent.heightCutoff = [2, 9] := rfl

def ChampionEvent.witness {ε : ℝ} (e : ChampionEvent ε) :
    Verdict (discrepancy ε e.champion = windowMaximum ε e.cutoff) :=
  .held e.reading (e.packet_calibrated)

theorem ChampionEvent.witness_is_B {ε : ℝ} (e : ChampionEvent ε) :
    e.witness.classify = (true, true) := rfl

def certifiedChampionTraceNineWitness :
    Verdict (∀ N ≤ 7, DisplacementAt (1/10) N ↔ N = 7) :=
  .held displacement_through_nine_iff certifiedChampionTraceNine_height_cutoffs

theorem certifiedChampionTraceNineWitness_is_B :
    certifiedChampionTraceNineWitness.classify = (true, true) := rfl

end Imscribing.ABC
