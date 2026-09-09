import Imscribing.ABC_MeasurementStream

namespace Imscribing.ABC

structure ChampionEvent (ε : ℝ) where
  /-- Lean window index; the Rust height cutoff is `cutoff + 2`. -/
  cutoff : ℕ
  previous : Option Triple
  champion : Triple
  member : champion ∈ arithmeticWindow cutoff
  reading : discrepancy ε champion = windowMaximum ε cutoff
  displaces : ∀ p, previous = some p → discrepancy ε p < discrepancy ε champion
  previous_reading : ∀ p, previous = some p → 0 < cutoff ∧
    discrepancy ε p = windowMaximum ε (cutoff - 1)

structure ChampionTrace (ε : ℝ) where
  events : List (ChampionEvent ε)
  ordered : List.Pairwise (fun x y => x.cutoff < y.cutoff) events
  initial : ∀ e, events.head? = some e → e.cutoff = 0 ∧ e.previous = none
  linked : ∀ i e f, events[i]? = some e → events[i+1]? = some f →
    f.previous = some e.champion
  stable_between : ∀ i e f, events[i]? = some e → events[i+1]? = some f →
    ∀ N, e.cutoff ≤ N → N < f.cutoff →
      windowMaximum ε N = discrepancy ε e.champion

def ChampionEvent.heightCutoff {ε : ℝ} (e : ChampionEvent ε) : ℕ := e.cutoff + 2

/-- A strict displacement of the exhaustive maximum, after initialization. -/
def DisplacementAt (ε : ℝ) (N : ℕ) : Prop :=
  0 < N ∧ windowMaximum ε (N - 1) < windowMaximum ε N

theorem ChampionEvent.displacement {ε : ℝ} (e : ChampionEvent ε)
    (p : Triple) (hp : e.previous = some p) : DisplacementAt ε e.cutoff := by
  obtain ⟨hn, hr⟩ := e.previous_reading p hp
  exact ⟨hn, by rw [← hr, ← e.reading]; exact e.displaces p hp⟩

theorem ChampionEvent.packet_calibrated {ε : ℝ} (e : ChampionEvent ε) :
    IUTT.weighted (arithmeticPacket e.champion) = logHeight e.champion ∧
      arithmeticPacket e.champion 0 = logRadical e.champion :=
  ⟨packet_height_calibration _, packet_radical_calibration _⟩

end Imscribing.ABC
