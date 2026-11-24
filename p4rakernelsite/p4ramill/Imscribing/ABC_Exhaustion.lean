import Imscribing.ABC_Spectral
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.LiminfLimsup

/-! # Exhaustive finite readings and their limit

Window N contains exactly the positive coprime triples with c ≤ N+2.
Its largest discrepancy is attained, increases with N, and converges to a
finite real limit precisely when the discrepancies have a uniform bound.
-/
namespace Imscribing.ABC

def baseTriple : Triple := ⟨1, 1, 2, by decide, by decide, rfl, by decide⟩

def pairTriple (N a b : ℕ) : Triple :=
  if h : 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a + b ≤ N + 2 then
    ⟨a, b, a + b, h.1, h.2.1, rfl, h.2.2.1⟩
  else baseTriple

noncomputable def arithmeticWindow (N : ℕ) : Finset Triple := by
  classical
  exact ((Finset.range (N + 3)).product (Finset.range (N + 3))).image
    (fun ab => pairTriple N ab.1 ab.2)

theorem pairTriple_height (N a b : ℕ) : (pairTriple N a b).c ≤ N + 2 := by
  unfold pairTriple
  split
  · rename_i h
    exact h.2.2.2
  · simp [baseTriple]

theorem mem_arithmeticWindow (N : ℕ) (t : Triple) :
    t ∈ arithmeticWindow N ↔ t.c ≤ N + 2 := by
  classical
  unfold arithmeticWindow
  constructor
  · intro h
    obtain ⟨ab, _, rfl⟩ := Finset.mem_image.mp h
    exact pairTriple_height N ab.1 ab.2
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(t.a, t.b), ?_, ?_⟩
    · have ha := t.a_pos
      have hb := t.b_pos
      have hs := t.sum_eq
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · have hs : t.a + t.b ≤ N + 2 := by rw [t.sum_eq]; exact h
      have hg : 0 < t.a ∧ 0 < t.b ∧ Nat.Coprime t.a t.b ∧ t.a + t.b ≤ N + 2 :=
        ⟨t.a_pos, t.b_pos, t.coprime, hs⟩
      dsimp only
      rw [pairTriple, dif_pos hg]
      cases t with
      | mk a b c ha hb he hc => cases he; rfl

theorem arithmeticWindow_nonempty (N : ℕ) : (arithmeticWindow N).Nonempty :=
  ⟨baseTriple, (mem_arithmeticWindow N baseTriple).mpr (by simp [baseTriple])⟩

theorem arithmeticWindow_monotone : Monotone arithmeticWindow := by
  intro N M h t ht
  exact (mem_arithmeticWindow M t).mpr
    ((mem_arithmeticWindow N t).mp ht |>.trans (Nat.add_le_add_right h 2))

theorem arithmeticWindow_exhaustive (t : Triple) : t ∈ arithmeticWindow t.c :=
  (mem_arithmeticWindow t.c t).mpr (by omega)

noncomputable def windowMaximum (ε : ℝ) (N : ℕ) : ℝ :=
  (arithmeticWindow N).sup' (arithmeticWindow_nonempty N) (discrepancy ε)

theorem discrepancy_le_windowMaximum (ε : ℝ) (N : ℕ) (t : Triple)
    (ht : t ∈ arithmeticWindow N) : discrepancy ε t ≤ windowMaximum ε N :=
  Finset.le_sup' (discrepancy ε) ht

theorem windowMaximum_le (ε C : ℝ) (N : ℕ)
    (h : ∀ t ∈ arithmeticWindow N, discrepancy ε t ≤ C) : windowMaximum ε N ≤ C :=
  Finset.sup'_le _ _ h

theorem windowMaximum_monotone (ε : ℝ) : Monotone (windowMaximum ε) := by
  intro N M h
  apply windowMaximum_le
  intro t ht
  exact discrepancy_le_windowMaximum ε M t (arithmeticWindow_monotone h ht)

theorem windowMaximum_attained (ε : ℝ) (N : ℕ) :
    ∃ t ∈ arithmeticWindow N, discrepancy ε t = windowMaximum ε N := by
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (arithmeticWindow N)
    (discrepancy ε) (arithmeticWindow_nonempty N)
  exact ⟨t, ht, le_antisymm (discrepancy_le_windowMaximum ε N t ht)
    (windowMaximum_le ε _ N hmax)⟩

noncomputable def windowFamily (N : ℕ) : Fin (arithmeticWindow N).card → Triple :=
  fun i => ((arithmeticWindow N).equivFin.symm i).val

theorem windowFamily_mem (N : ℕ) (i : Fin (arithmeticWindow N).card) :
    windowFamily N i ∈ arithmeticWindow N :=
  ((arithmeticWindow N).equivFin.symm i).property

theorem windowMaximum_is_largest_eigenvalue (ε : ℝ) (N : ℕ) :
    ArithmeticEigenvalue (windowFamily N) ε (windowMaximum ε N) ∧
      ∀ value, ArithmeticEigenvalue (windowFamily N) ε value →
        value ≤ windowMaximum ε N := by
  constructor
  · obtain ⟨t, ht, he⟩ := windowMaximum_attained ε N
    apply (arithmeticEigenvalue_iff _ _ _).mpr
    refine ⟨(arithmeticWindow N).equivFin ⟨t, ht⟩, ?_⟩
    simpa only [windowFamily, Equiv.symm_apply_apply] using he
  · intro value hv
    obtain ⟨i, rfl⟩ := (arithmeticEigenvalue_iff _ _ _).mp hv
    exact discrepancy_le_windowMaximum ε N _ (windowFamily_mem N i)

theorem window_bounded_iff_discrepancy (ε : ℝ) :
    BddAbove (Set.range (windowMaximum ε)) ↔ ∃ C : ℝ, ∀ t, discrepancy ε t ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun t => ?_⟩
    exact (discrepancy_le_windowMaximum ε t.c t (arithmeticWindow_exhaustive t)).trans
      (hC (Set.mem_range_self t.c))
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact windowMaximum_le ε C N (fun t _ => hC t)

/-- A finite limit is a theorem about every scale, not a finite plot. -/
theorem window_converges_iff_bounded (ε : ℝ) :
    (∃ L : ℝ, Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L)) ↔
      BddAbove (Set.range (windowMaximum ε)) := by
  constructor
  · rintro ⟨L, hL⟩
    exact hL.bddAbove_range
  · intro h
    exact ⟨_, tendsto_atTop_ciSup (windowMaximum_monotone ε) h⟩

theorem abc_iff_window_convergence : Conjecture ↔
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      Filter.Tendsto (windowMaximum ε) Filter.atTop (nhds L) := by
  rw [conjecture_iff_uniform_discrepancy]
  constructor
  · intro h ε hε
    exact (window_converges_iff_bounded ε).mpr
      ((window_bounded_iff_discrepancy ε).mpr (h ε hε))
  · intro h ε hε
    exact (window_bounded_iff_discrepancy ε).mp
      ((window_converges_iff_bounded ε).mp (h ε hε))

end Imscribing.ABC
