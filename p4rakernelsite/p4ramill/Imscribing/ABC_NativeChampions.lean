import Imscribing.Paraconsistent.DialetheicWitness

namespace Imscribing.ABC

inductive TrilatticeState where
  | N | T | F | B
  deriving DecidableEq, Repr

structure ChampionCertificate where
  cutoff : Nat
  a : Nat
  b : Nat
  c : Nat
  state : TrilatticeState

def nativeChampionTrace : List ChampionCertificate :=
  [ { cutoff := 2, a := 1, b := 1, c := 2, state := .B },
  { cutoff := 9, a := 1, b := 8, c := 9, state := .B } ]

theorem nativeChampionTrace_is_B :
    ∀ event ∈ nativeChampionTrace, event.state = .B := by
  intro event h
  simp [nativeChampionTrace] at h
  aesop

end Imscribing.ABC
