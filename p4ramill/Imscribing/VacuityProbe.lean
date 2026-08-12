import Imscribing.Millennium.ErdosFormalize
open Filter Finset
open scoped BigOperators Classical

example : ErdosFormalize.RamseyOddCycleTriangleLimit := by
  unfold ErdosFormalize.RamseyOddCycleTriangleLimit
  intro n _
  exact ⟨1/2, by norm_num, by norm_num⟩

example : ErdosFormalize.ErdosUnbounded := by
  unfold ErdosFormalize.ErdosUnbounded
  intro z _ M
  obtain ⟨n, hn⟩ := exists_nat_ge M
  exact ⟨n, hn⟩
