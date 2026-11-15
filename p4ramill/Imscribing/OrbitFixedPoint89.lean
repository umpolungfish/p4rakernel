import Mathlib

open scoped BigOperators

namespace Imscribing.ThreeBody.OrbitFixedPoint89

abbrev Body := Fin 3
abbrev Vec3 := Fin 3 → ℝ

structure PhaseState where
  pos : Body → Vec3
  vel : Body → Vec3

abbrev Orbit := ℝ → PhaseState

namespace Orbit

def tail (σ : Orbit) (t : ℝ) : Orbit := fun τ => σ (τ + t)

theorem tail_tail (σ : Orbit) (s t : ℝ) :
    (σ.tail s).tail t = σ.tail (s + t) := by
  funext τ
  show σ ((τ + t) + s) = σ (τ + (s + t))
  rw [show (τ + t) + s = τ + (s + t) from by ring]

theorem self_reference (σ : Orbit) (t : ℝ) :
    (σ.tail t).tail (-t) = σ := by
  funext τ; simp [tail]

theorem has_tail (σ : Orbit) (t : ℝ) :
    ∃ σ' : Orbit, σ'.tail (-t) = σ :=
  ⟨σ.tail t, self_reference σ t⟩

theorem tails_closed (σ : Orbit) (s t : ℝ) :
    ∃ u : ℝ, σ.tail u = (σ.tail s).tail t :=
  ⟨s + t, (tail_tail σ s t).symm⟩

end Orbit

noncomputable section
open Classical

def Vec3.normSq (v : Vec3) : ℝ := ∑ (c : Fin 3), v c * v c

def Vec3.invCube (v : Vec3) : ℝ :=
  1 / (v.normSq * Real.sqrt v.normSq)

structure ThreeBodyParameters where
  G : ℝ
  mass : Body → ℝ
  G_pos : 0 < G
  mass_pos : ∀ i, 0 < mass i

def sep (s : PhaseState) (i j : Body) : Vec3 :=
  fun (c : Fin 3) => s.pos j c - s.pos i c

def accel (p : ThreeBodyParameters) (s : PhaseState) (i : Body) : Vec3 :=
  fun (c : Fin 3) => p.G * ∑ (j : Body),
    if h : i ≠ j then (p.mass j * (sep s i j).invCube) * (sep s i j) c else 0

def vectorField (p : ThreeBodyParameters) (s : PhaseState) : PhaseState where
  pos := s.vel
  vel := fun (i : Body) => accel p s i

def IsNewtonianOrbit (p : ThreeBodyParameters) (σ : Orbit) : Prop :=
  (∀ (i : Body) (c : Fin 3), Continuous (fun t => (σ t).vel i c)) ∧
  (∀ (t : ℝ) (i : Body) (c : Fin 3),
    HasDerivAt (fun τ => (σ τ).pos i c) ((σ t).vel i c) t ∧
    HasDerivAt (fun τ => (σ τ).vel i c) (accel p (σ t) i c) t)

theorem tail_is_newtonian (p : ThreeBodyParameters) (σ : Orbit)
    (hσ : IsNewtonianOrbit p σ) (t : ℝ) :
    IsNewtonianOrbit p (σ.tail t) := by
  refine ⟨?_, ?_⟩
  · intro i c
    show Continuous (fun τ => (σ (τ + t)).vel i c)
    exact (hσ.1 i c).comp (continuous_id.add continuous_const)
  · intro u i c
    have hg : HasDerivAt (fun y : ℝ => y + t) 1 u :=
      (hasDerivAt_id u).add_const t
    have h1 : HasDerivAt (fun τ => (σ (τ + t)).pos i c)
        ((σ (u + t)).vel i c) u := by
      have hcomp := (hσ.2 (u + t) i c).1.comp u hg
      simpa [Function.comp_apply, mul_one] using hcomp
    have h2 : HasDerivAt (fun τ => (σ (τ + t)).vel i c)
        (accel p (σ (u + t)) i c) u := by
      have hcomp := (hσ.2 (u + t) i c).2.comp u hg
      simpa [Function.comp_apply, mul_one] using hcomp
    exact ⟨h1, h2⟩

def stateDist (s₁ s₂ : PhaseState) : ℝ :=
  ∑ (i : Body), ∑ (c : Fin 3),
    (s₁.pos i c - s₂.pos i c)^2 + (s₁.vel i c - s₂.vel i c)^2

def constantPredictor (σ : Orbit) (_t : ℝ) : PhaseState := σ 0

def eulerPredictor (p : ThreeBodyParameters) (σ : Orbit) (t : ℝ) : PhaseState where
  pos := fun (i : Body) (c : Fin 3) => (σ 0).pos i c + t * (σ 0).vel i c
  vel := fun (i : Body) (c : Fin 3) => (σ 0).vel i c + t * accel p (σ 0) i c

theorem predictive_superiority
    {e_low e_high : ℝ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hlow  : ∀ t, 0 < t → c * t ≤ e_low t)
    (hhigh : ∀ t, 0 < t → e_high t ≤ C * t^2) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → e_high t < e_low t := by
  refine ⟨c / (C + 1), div_pos hc (by linarith), fun t ht htδ => ?_⟩
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hne : C + 1 ≠ 0 := ne_of_gt hC1
  have hCt : C * t < c := by
    have h1 : t * (C + 1) < c := by
      have hstep := mul_lt_mul_of_pos_right htδ hC1
      have heq : c / (C + 1) * (C + 1) = c := div_mul_cancel₀ c hne
      linarith
    nlinarith [h1, ht]
  calc e_high t ≤ C * t^2 := hhigh t ht
    _ = (C * t) * t := by ring
    _ < c * t := mul_lt_mul_of_pos_right hCt ht
    _ ≤ e_low t := hlow t ht

theorem newtonian_predictive_superiority
    (p : ThreeBodyParameters) (σ : Orbit)
    (drift C : ℝ) (hdrift : 0 < drift) (hC : 0 ≤ C)
    (h_low : ∀ t, 0 < t →
      drift * t ≤ stateDist (σ t) (constantPredictor σ t))
    (h_high : ∀ t, 0 < t →
      stateDist (σ t) (eulerPredictor p σ t) ≤ C * t^2) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      stateDist (σ t) (eulerPredictor p σ t) <
      stateDist (σ t) (constantPredictor σ t) :=
  predictive_superiority hdrift hC h_low h_high

end

namespace Operational

structure FState where
  pos : Body → Fin 3 → Float
  vel : Body → Fin 3 → Float

def sepF (s : FState) (i j : Body) : Fin 3 → Float :=
  fun c => s.pos j c - s.pos i c

def normSqF (v : Fin 3 → Float) : Float :=
  v 0 * v 0 + v 1 * v 1 + v 2 * v 2

def invCubeF (v : Fin 3 → Float) : Float :=
  let n := normSqF v
  1.0 / (n * n * n)

def massF : Fin 3 → Float := ![1.0, 1.0, 1.0]
def GF : Float := 1.0

def accelF (s : FState) (i : Body) : Fin 3 → Float :=
  fun c =>
    GF * ((if i ≠ 0 then massF 0 * invCubeF (sepF s i 0) * sepF s i 0 c else 0.0) +
           (if i ≠ 1 then massF 1 * invCubeF (sepF s i 1) * sepF s i 1 c else 0.0) +
           (if i ≠ 2 then massF 2 * invCubeF (sepF s i 2) * sepF s i 2 c else 0.0))

def eulerStep (dt : Float) (s : FState) : FState where
  pos := fun (i : Body) (c : Fin 3) => s.pos i c + dt * s.vel i c
  vel := fun (i : Body) (c : Fin 3) => s.vel i c + dt * accelF s i c

def initState : FState where
  pos := fun i => ![![0.0, 0.0, 0.0], ![1.0, 0.0, 0.0], ![0.0, 1.0, 0.0]] i
  vel := fun i => ![![1.0, 0.0, 0.0], ![0.0, 0.0, 0.0], ![0.0, 0.0, 0.0]] i

def iterateEuler (n : Nat) (dt : Float) : FState :=
  Nat.rec (motive := fun _ => FState) initState (fun _ s => eulerStep dt s) n

#eval (eulerStep 0.01 initState).pos 0 0
#eval (eulerStep 0.01 initState).vel 0 0
#eval (iterateEuler 10 0.001).pos 0 0

end Operational

end Imscribing.ThreeBody.OrbitFixedPoint89