import Mathlib
open Matrix Filter
noncomputable section
namespace PlaquetteReflection
abbrev Site (Ls Lt : ℕ) := (Fin 3 → ZMod Ls) × ZMod Lt
abbrev Gauge (N Ls Lt : ℕ) := Site Ls Lt → Fin 4 → unitaryGroup (Fin N) ℂ
variable {N Ls Lt : ℕ}
def unit (Ls Lt : ℕ) (μ : Fin 4) : Site Ls Lt :=
  (fun i : Fin 3 => if i.succ = μ then (1 : ZMod Ls) else 0,
   if μ = 0 then (1 : ZMod Lt) else 0)
def plaq (U : Gauge N Ls Lt) (x : Site Ls Lt) (μ ν : Fin 4) : unitaryGroup (Fin N) ℂ :=
  U x μ * U (x + unit Ls Lt μ) ν * (U (x + unit Ls Lt ν) μ)⁻¹ * (U x ν)⁻¹
def wilson (U : Gauge N Ls Lt) (x : Site Ls Lt) (μ ν : Fin 4) : ℝ :=
  (1 / (N : ℝ)) * ((((plaq U x μ ν : unitaryGroup (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ).trace).re
def timeRefl (p : Site Ls Lt) : Site Ls Lt := (p.1, -p.2)
def shiftBy (k : Fin 3 → ℤ) (p : Site Ls Lt) : Site Ls Lt :=
  (fun i => p.1 i + (k i : ZMod Ls), p.2)
theorem timeRefl_involutive : Function.Involutive (timeRefl : Site Ls Lt → Site Ls Lt) := by intro p; simp [timeRefl]
theorem timeRefl_zero : timeRefl (0 : Site Ls Lt) = 0 := by apply Prod.ext <;> simp [timeRefl]
theorem exists_timeRefl_fixed : ∃ p : Site Ls Lt, timeRefl p = p := ⟨0, timeRefl_zero⟩
def ReflEq (U : Gauge N Ls Lt) : Prop := ∀ (x : Site Ls Lt) (μ ν : Fin 4), μ < ν → wilson U x μ ν = wilson U (timeRefl x) μ ν
def ShiftEq (U : Gauge N Ls Lt) : Prop := ∀ (x : Site Ls Lt) (μ ν : Fin 4) (k : Fin 3 → ℤ), μ < ν → wilson U (timeRefl x) μ ν = wilson U (shiftBy k (timeRefl x)) μ ν
def TripleId (U : Gauge N Ls Lt) : Prop := ∀ (x : Site Ls Lt) (μ ν : Fin 4) (k : Fin 3 → ℤ), μ < ν → wilson U x μ ν = wilson U (timeRefl x) μ ν ∧ wilson U (timeRefl x) μ ν = wilson U (shiftBy k (timeRefl x)) μ ν
def WindingQuant (A : Site Ls Lt → Fin 4 → Fin 4 → ℝ) (wind : Site Ls Lt → Fin 4 → Fin 4 → ℤ) : Prop :=
  ∀ (x : Site Ls Lt) (μ ν : Fin 4), μ < ν → ∃ n : ℕ, n < 2 ^ 32 ∧ A x μ ν = 2 * (n : ℝ) ∧ wind x μ ν ≠ 0
structure RankedUniverse where
  Cfg : Type
  mem : Cfg → Cfg → Prop
  rank : Cfg → ℕ
  rank_lt : ∀ {y x : Cfg}, mem y x → rank y < rank x
  chiral2 : ∃ x y z : Cfg, mem y x ∧ mem z y ∧ ¬ mem z x ∧ rank z < rank y
theorem RankedUniverse.mem_wf (R : RankedUniverse) : WellFounded R.mem :=
  Subrelation.wf (r := fun a b => R.rank a < R.rank b) (fun {a b} h => R.rank_lt h) (InvImage.wf R.rank wellFounded_lt)
structure CriticalRG where
  X : Type
  Y : Type
  δ : X → Y
  mu : Y → X
  rg_id : mu ∘ δ = id
  ξ : ℕ → ℝ
  ξ_diverges : Tendsto ξ atTop atTop
structure Core (N Ls Lt : ℕ) (𝔸 : Type) [Ring 𝔸] [Algebra ℂ 𝔸] where
  U : Gauge N Ls Lt
  det_one : ∀ x μ, (((U x μ : unitaryGroup (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ).det = 1
  triple : TripleId U
  carrier_surj : ∀ (x : Site Ls Lt) (μ ν : Fin 4), μ < ν → Function.Surjective (fun V : Gauge N Ls Lt => plaq V x μ ν)
  loopA : Site Ls Lt → Fin 4 → Fin 4 → ℝ
  wind : Site Ls Lt → Fin 4 → Fin 4 → ℤ
  winding : WindingQuant loopA wind
  X : 𝔸
  P : 𝔸
  hbar : ℝ
  hbar_pos : 0 < hbar
  ccr : X * P - P * X = (Complex.I * (hbar : ℂ)) • (1 : 𝔸)
  x0 : ℤ
  x0_ne : x0 ≠ 0
  x0_even : Even x0
  τ : ℝ
  T : ℝ
  T_pos : 0 < T
  frozen : 1000 * T ≤ τ
  ranked : RankedUniverse
  rg : CriticalRG
  prec : Site Ls Lt → Site Ls Lt → Prop
  prec_asymm : ∀ a b, prec a b → ¬ prec b a
  k0 : Fin 3 → ℤ
  oriented : ∀ x, prec x (shiftBy k0 (timeRefl x))
  wRefl : ℕ
  wShift : ℕ
  wRefl_eq : wRefl = 1
  wShift_eq : wShift = 1
structure Full (N Ls Lt : ℕ) (𝔸 : Type) [Ring 𝔸] [Algebra ℂ 𝔸] extends Core N Ls Lt 𝔸 where
  fixed_point_free : ∀ x : Site Ls Lt, timeRefl x ≠ x
section theorems
variable {𝔸 : Type} [Ring 𝔸] [Algebra ℂ 𝔸]
theorem Core.grammar (C : Core N Ls Lt 𝔸) : (ReflEq C.U ∧ ShiftEq C.U) ∧ WindingQuant C.loopA C.wind :=
  ⟨⟨fun x μ ν h => (C.triple x μ ν 0 h).1, fun x μ ν k h => (C.triple x μ ν k h).2⟩, C.winding⟩
theorem Core.wilson_eq_shifted (C : Core N Ls Lt 𝔸) (x : Site Ls Lt) (μ ν : Fin 4) (k : Fin 3 → ℤ) (h : μ < ν) :
    wilson C.U x μ ν = wilson C.U (shiftBy k (timeRefl x)) μ ν :=
  ((C.triple x μ ν k h).1).trans (C.triple x μ ν k h).2
theorem Core.wind_ne_zero (C : Core N Ls Lt 𝔸) (x : Site Ls Lt) (μ ν : Fin 4) (h : μ < ν) : C.wind x μ ν ≠ 0 := by
  obtain ⟨_, _, _, hw⟩ := C.winding x μ ν h; exact hw
theorem Core.loopA_quantized (C : Core N Ls Lt 𝔸) (x : Site Ls Lt) (μ ν : Fin 4) (h : μ < ν) :
    ∃ n : ℕ, n < 2 ^ 32 ∧ C.loopA x μ ν = 2 * (n : ℝ) := by
  obtain ⟨n, hn, hA, _⟩ := C.winding x μ ν h; exact ⟨n, hn, hA⟩
theorem Core.mem_wf (C : Core N Ls Lt 𝔸) : WellFounded C.ranked.mem := C.ranked.mem_wf
theorem Core.zero_mode_abs_ge_two (C : Core N Ls Lt 𝔸) : 2 ≤ |C.x0| := by
  obtain ⟨m, hm⟩ := C.x0_even
  have hm0 : m ≠ 0 := by rintro rfl; exact C.x0_ne (by simpa using hm)
  have h1 : 1 ≤ |m| := Int.one_le_abs hm0
  have h2 : |C.x0| = 2 * |m| := by rw [hm, ← two_mul, abs_mul]; norm_num
  omega
theorem Full.isEmpty : IsEmpty (Full N Ls Lt 𝔸) := ⟨fun F => F.fixed_point_free 0 timeRefl_zero⟩
end theorems
end PlaquetteReflection
