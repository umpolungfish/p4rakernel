import Mathlib

/-!
# GravityOrganism89

A single-file formalization of the relational Newtonian three-body organism.

The physical core is expressed in the three oriented side-vectors

  s₁ = x₃ - x₂,   s₂ = x₁ - x₃,   s₃ = x₂ - x₁.

The file contains:
* the exact symmetric relational acceleration law and its equivalence to
  the three body accelerations;
* closure/tangency of the relational dynamics;
* instantaneous linear-momentum, angular-momentum, and energy-rate identities;
* Galilean translation/boost cancellation and orthogonal-frame equivariance;
* the integral fixed-point formulation of the full coupled evolution;
* the nonterminal integer-indexed hierarchy;
* a lifted winding certificate for periodic fixed-point histories;
* the critical reduced shape block and its defective (exceptional-point) kernel.

No global existence, collision continuation, or arbitrary-orbit periodicity is
silently assumed.  The history structure describes a global collision-free
branch; the collision boundary is separately stratified, and continuation
through a collision must be supplied as additional regularized history data.
-/

noncomputable section

namespace Imscribing.ThreeBody

/-! ## Euclidean three-vectors -/

abbrev Vec3 := Fin 3 → ℝ

/-- The Euclidean inner product on coordinate triples. -/
def dot (u v : Vec3) : ℝ := ∑ i : Fin 3, u i * v i

/-- Squared Euclidean length. -/
def normSq (u : Vec3) : ℝ := dot u u

lemma dot_add_left (u v w : Vec3) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, Finset.sum_add_distrib, add_mul]

lemma dot_add_right (u v w : Vec3) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, Finset.sum_add_distrib, mul_add]

lemma dot_sub_left (u v w : Vec3) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, Finset.sum_sub_distrib, sub_mul]

lemma dot_sub_right (u v w : Vec3) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, Finset.sum_sub_distrib, mul_sub]

lemma dot_smul_left (a : ℝ) (u v : Vec3) : dot (a • u) v = a * dot u v := by
  simp [dot, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma dot_smul_right (a : ℝ) (u v : Vec3) : dot u (a • v) = a * dot u v := by
  simp [dot, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma dot_comm (u v : Vec3) : dot u v = dot v u := by
  simp [dot, mul_comm]

/-- The oriented cross product in three coordinates. -/
def cross (u v : Vec3) : Vec3 := fun i =>
  if i = 0 then u 1 * v 2 - u 2 * v 1
  else if i = 1 then u 2 * v 0 - u 0 * v 2
  else u 0 * v 1 - u 1 * v 0

lemma cross_self (u : Vec3) : cross u u = 0 := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-! ## Parameters and the three-body configuration -/

structure Parameters where
  G  : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  hG  : 0 < G
  hm1 : 0 < m1
  hm2 : 0 < m2
  hm3 : 0 < m3

namespace Parameters

def totalMass (p : Parameters) : ℝ := p.m1 + p.m2 + p.m3

def sigma₂ (p : Parameters) : ℝ :=
  p.m1 * p.m2 + p.m2 * p.m3 + p.m3 * p.m1

end Parameters

structure Configuration where
  x1 : Vec3
  x2 : Vec3
  x3 : Vec3

structure Velocities where
  v1 : Vec3
  v2 : Vec3
  v3 : Vec3

/-- Side opposite body 1. -/
def s1 (x : Configuration) : Vec3 := x.x3 - x.x2

/-- Side opposite body 2. -/
def s2 (x : Configuration) : Vec3 := x.x1 - x.x3

/-- Side opposite body 3. -/
def s3 (x : Configuration) : Vec3 := x.x2 - x.x1

/-- The oriented sides close identically. -/
theorem sides_close (x : Configuration) : s1 x + s2 x + s3 x = 0 := by
  ext i
  simp [s1, s2, s3]

/-- Newton's inverse-cube kernel, `r / ‖r‖³`, in a form using squared length. -/
def invCube (r : Vec3) : ℝ := 1 / (normSq r * Real.sqrt (normSq r))

theorem invCube_pos (r : Vec3) (h : 0 < normSq r) : 0 < invCube r := by
  unfold invCube
  apply div_pos one_pos
  exact mul_pos h (Real.sqrt_pos.2 h)

/-- Collision-free side condition. -/
def SideCollisionFree (x : Configuration) : Prop :=
  0 < normSq (s1 x) ∧ 0 < normSq (s2 x) ∧ 0 < normSq (s3 x)

/-- The singular set of the Newtonian three-body configuration space. -/
def CollisionBoundary (x : Configuration) : Prop :=
  s1 x = 0 ∨ s2 x = 0 ∨ s3 x = 0

/-- Binary collision of bodies 1 and 2. -/
def BinaryCollision12 (x : Configuration) : Prop := s3 x = 0

/-- Binary collision of bodies 2 and 3. -/
def BinaryCollision23 (x : Configuration) : Prop := s1 x = 0

/-- Binary collision of bodies 3 and 1. -/
def BinaryCollision31 (x : Configuration) : Prop := s2 x = 0

/-- Triple collision: all three bodies occupy the same position. -/
def TripleCollision (x : Configuration) : Prop :=
  s1 x = 0 ∧ s2 x = 0 ∧ s3 x = 0

/-- Side closure forces the third side to vanish when the other two vanish. -/
theorem s1_s2_zero_imp_s3_zero (x : Configuration)
    (h1 : s1 x = 0) (h2 : s2 x = 0) : s3 x = 0 := by
  have h := sides_close x
  simpa [h1, h2] using h

theorem s1_s3_zero_imp_s2_zero (x : Configuration)
    (h1 : s1 x = 0) (h3 : s3 x = 0) : s2 x = 0 := by
  have h := sides_close x
  simpa [h1, h3] using h

theorem s2_s3_zero_imp_s1_zero (x : Configuration)
    (h2 : s2 x = 0) (h3 : s3 x = 0) : s1 x = 0 := by
  have h := sides_close x
  simpa [h2, h3] using h

/-- Every point on the collision boundary belongs either to the triple-collision
stratum or to exactly one binary-collision stratum. -/
theorem collision_boundary_classification (x : Configuration)
    (h : CollisionBoundary x) :
    TripleCollision x ∨
    (BinaryCollision23 x ∧ s2 x ≠ 0 ∧ s3 x ≠ 0) ∨
    (BinaryCollision31 x ∧ s1 x ≠ 0 ∧ s3 x ≠ 0) ∨
    (BinaryCollision12 x ∧ s1 x ≠ 0 ∧ s2 x ≠ 0) := by
  rcases h with h1 | h2 | h3
  · by_cases h2' : s2 x = 0
    · exact Or.inl ⟨h1, h2', s1_s2_zero_imp_s3_zero x h1 h2'⟩
    · right
      left
      refine ⟨h1, h2', ?_⟩
      intro h3'
      exact h2' (s1_s3_zero_imp_s2_zero x h1 h3')
  · by_cases h3' : s3 x = 0
    · exact Or.inl ⟨s2_s3_zero_imp_s1_zero x h2 h3', h2, h3'⟩
    · right
      right
      left
      refine ⟨h2, ?_, h3'⟩
      intro h1'
      exact h3' (s1_s2_zero_imp_s3_zero x h1' h2)
  · by_cases h1' : s1 x = 0
    · exact Or.inl ⟨h1', s1_s3_zero_imp_s2_zero x h1' h3, h3⟩
    · right
      right
      right
      refine ⟨h3, h1', ?_⟩
      intro h2'
      exact h1' (s2_s3_zero_imp_s1_zero x h2' h3)

/-! ## Newtonian body accelerations and their relational form -/

/-- Acceleration of body 1, obtained from the forces due to bodies 2 and 3. -/
def bodyAcc1 (p : Parameters) (x : Configuration) : Vec3 :=
  p.G • ((p.m2 * invCube (s3 x)) • s3 x -
         (p.m3 * invCube (s2 x)) • s2 x)

/-- Acceleration of body 2. -/
def bodyAcc2 (p : Parameters) (x : Configuration) : Vec3 :=
  p.G • ((p.m3 * invCube (s1 x)) • s1 x -
         (p.m1 * invCube (s3 x)) • s3 x)

/-- Acceleration of body 3. -/
def bodyAcc3 (p : Parameters) (x : Configuration) : Vec3 :=
  p.G • ((p.m1 * invCube (s2 x)) • s2 x -
         (p.m2 * invCube (s1 x)) • s1 x)

/-- Pair force on body 1 from body 2. -/
def force12 (p : Parameters) (x : Configuration) : Vec3 :=
  (p.G * p.m1 * p.m2 * invCube (s3 x)) • s3 x

/-- Pair force on body 2 from body 3. -/
def force23 (p : Parameters) (x : Configuration) : Vec3 :=
  (p.G * p.m2 * p.m3 * invCube (s1 x)) • s1 x

/-- Pair force on body 3 from body 1. -/
def force31 (p : Parameters) (x : Configuration) : Vec3 :=
  (p.G * p.m3 * p.m1 * invCube (s2 x)) • s2 x

/-- Reaction force on body 2 from body 1. -/
def force21 (p : Parameters) (x : Configuration) : Vec3 := -(force12 p x)

/-- Reaction force on body 3 from body 2. -/
def force32 (p : Parameters) (x : Configuration) : Vec3 := -(force23 p x)

/-- Reaction force on body 1 from body 3. -/
def force13 (p : Parameters) (x : Configuration) : Vec3 := -(force31 p x)

/-- Net Newtonian forces on the three bodies, grouped by unordered pair. -/
def netForce1 (p : Parameters) (x : Configuration) : Vec3 :=
  force12 p x - force31 p x

def netForce2 (p : Parameters) (x : Configuration) : Vec3 :=
  force23 p x - force12 p x

def netForce3 (p : Parameters) (x : Configuration) : Vec3 :=
  force31 p x - force23 p x

/-- Newton's second law holds body by body. -/
theorem newton_second_law_body1 (p : Parameters) (x : Configuration) :
    p.m1 • bodyAcc1 p x = netForce1 p x := by
  ext i
  simp [bodyAcc1, netForce1, force12, force31, s1, s2, s3]
  ring

theorem newton_second_law_body2 (p : Parameters) (x : Configuration) :
    p.m2 • bodyAcc2 p x = netForce2 p x := by
  ext i
  simp [bodyAcc2, netForce2, force23, force12, s1, s2, s3]
  ring

theorem newton_second_law_body3 (p : Parameters) (x : Configuration) :
    p.m3 • bodyAcc3 p x = netForce3 p x := by
  ext i
  simp [bodyAcc3, netForce3, force31, force23, s1, s2, s3]
  ring

/-- Each pair interaction satisfies Newton's action-reaction law. -/
theorem pair_force_reaction12 (p : Parameters) (x : Configuration) :
    force12 p x + force21 p x = 0 := by
  simp [force21]

theorem pair_force_reaction23 (p : Parameters) (x : Configuration) :
    force23 p x + force32 p x = 0 := by
  simp [force32]

theorem pair_force_reaction31 (p : Parameters) (x : Configuration) :
    force31 p x + force13 p x = 0 := by
  simp [force13]

/-- The shared relational gravitational field. -/
def sharedField (r1 r2 r3 : Vec3) : Vec3 :=
  invCube r1 • r1 + invCube r2 • r2 + invCube r3 • r3

/-- Exact acceleration law for side 1. -/
def relationalAcc1 (p : Parameters) (r1 r2 r3 : Vec3) : Vec3 :=
  p.G • (p.m1 • sharedField r1 r2 r3 -
    (p.totalMass * invCube r1) • r1)

/-- Exact acceleration law for side 2. -/
def relationalAcc2 (p : Parameters) (r1 r2 r3 : Vec3) : Vec3 :=
  p.G • (p.m2 • sharedField r1 r2 r3 -
    (p.totalMass * invCube r2) • r2)

/-- Exact acceleration law for side 3. -/
def relationalAcc3 (p : Parameters) (r1 r2 r3 : Vec3) : Vec3 :=
  p.G • (p.m3 • sharedField r1 r2 r3 -
    (p.totalMass * invCube r3) • r3)

/-- The relational equation is exactly the difference `a₃ - a₂`. -/
theorem relationalAcc1_eq_body (p : Parameters) (x : Configuration) :
    relationalAcc1 p (s1 x) (s2 x) (s3 x) = bodyAcc3 p x - bodyAcc2 p x := by
  ext i
  simp [relationalAcc1, bodyAcc2, bodyAcc3, sharedField,
    Parameters.totalMass, s1, s2, s3]
  ring

/-- The relational equation is exactly the difference `a₁ - a₃`. -/
theorem relationalAcc2_eq_body (p : Parameters) (x : Configuration) :
    relationalAcc2 p (s1 x) (s2 x) (s3 x) = bodyAcc1 p x - bodyAcc3 p x := by
  ext i
  simp [relationalAcc2, bodyAcc1, bodyAcc3, sharedField,
    Parameters.totalMass, s1, s2, s3]
  ring

/-- The relational equation is exactly the difference `a₂ - a₁`. -/
theorem relationalAcc3_eq_body (p : Parameters) (x : Configuration) :
    relationalAcc3 p (s1 x) (s2 x) (s3 x) = bodyAcc2 p x - bodyAcc1 p x := by
  ext i
  simp [relationalAcc3, bodyAcc1, bodyAcc2, sharedField,
    Parameters.totalMass, s1, s2, s3]
  ring

/-- The three relational accelerations always close. -/
theorem relational_accelerations_close (p : Parameters) (r1 r2 r3 : Vec3) :
    relationalAcc1 p r1 r2 r3 +
    relationalAcc2 p r1 r2 r3 +
    relationalAcc3 p r1 r2 r3 = 0 := by
  ext i
  simp [relationalAcc1, relationalAcc2, relationalAcc3,
    sharedField, Parameters.totalMass]
  ring

/-! ## Instantaneous conservation identities -/

/-- Mass-weighted acceleration, i.e. the instantaneous rate of total momentum. -/
def momentumRate (p : Parameters) (x : Configuration) : Vec3 :=
  p.m1 • bodyAcc1 p x + p.m2 • bodyAcc2 p x + p.m3 • bodyAcc3 p x

/-- Internal gravitational forces cancel pairwise: total momentum rate is zero. -/
theorem momentum_rate_zero (p : Parameters) (x : Configuration) :
    momentumRate p x = 0 := by
  ext i
  simp [momentumRate, bodyAcc1, bodyAcc2, bodyAcc3, s1, s2, s3]
  ring

/-- Kinetic-energy directional rate at a state. -/
def kineticPower (p : Parameters) (x : Configuration) (v : Velocities) : ℝ :=
  p.m1 * dot (bodyAcc1 p x) v.v1 +
  p.m2 * dot (bodyAcc2 p x) v.v2 +
  p.m3 * dot (bodyAcc3 p x) v.v3

/-- Directional rate of the Newtonian pair potential along the velocity state.
This is the chain-rule expression for
`-G Σ_{i<j} mᵢmⱼ / ‖xᵢ-xⱼ‖`. -/
def potentialEnergyDirectionalRate
    (p : Parameters) (x : Configuration) (v : Velocities) : ℝ :=
  p.G * (
    p.m1 * p.m2 * invCube (s3 x) * dot (s3 x) (v.v2 - v.v1) +
    p.m2 * p.m3 * invCube (s1 x) * dot (s1 x) (v.v3 - v.v2) +
    p.m3 * p.m1 * invCube (s2 x) * dot (s2 x) (v.v1 - v.v3))

/-- The kinetic and potential directional rates cancel exactly. -/
theorem energy_rate_zero (p : Parameters) (x : Configuration) (v : Velocities) :
    kineticPower p x v + potentialEnergyDirectionalRate p x v = 0 := by
  simp [kineticPower, potentialEnergyDirectionalRate,
    bodyAcc1, bodyAcc2, bodyAcc3,
    dot_smul_left, dot_sub_left, dot_sub_right]
  ring

/-- Instantaneous torque rate about the chosen origin. -/
def torqueRate (p : Parameters) (x : Configuration) : Vec3 :=
  p.m1 • cross x.x1 (bodyAcc1 p x) +
  p.m2 • cross x.x2 (bodyAcc2 p x) +
  p.m3 • cross x.x3 (bodyAcc3 p x)

/-- Internal gravitational forces have zero total torque because each pair force
is parallel to its separation vector. -/
theorem torque_rate_zero (p : Parameters) (x : Configuration) :
    torqueRate p x = 0 := by
  ext i
  fin_cases i <;>
    simp [torqueRate, bodyAcc1, bodyAcc2, bodyAcc3, cross, s1, s2, s3] <;>
    ring

/-! ## Galilean and orthogonal-frame covariance -/

/-- A common translation of all bodies leaves the side vectors unchanged. -/
def translateConfig (a : Vec3) (x : Configuration) : Configuration :=
  ⟨x.x1 + a, x.x2 + a, x.x3 + a⟩

theorem sides_translation_invariant (a : Vec3) (x : Configuration) :
    s1 (translateConfig a x) = s1 x ∧
    s2 (translateConfig a x) = s2 x ∧
    s3 (translateConfig a x) = s3 x := by
  constructor
  · ext i
    simp [translateConfig, s1, s2, s3]
  constructor
  · ext i
    simp [translateConfig, s1, s2, s3]
  · ext i
    simp [translateConfig, s1, s2, s3]

/-- A common velocity boost leaves all relative velocities unchanged. -/
def boostVelocities (b : Vec3) (v : Velocities) : Velocities :=
  ⟨v.v1 + b, v.v2 + b, v.v3 + b⟩

theorem relative_velocity_boost_invariant (b : Vec3) (v : Velocities) :
    (boostVelocities b v).v2 - (boostVelocities b v).v1 = v.v2 - v.v1 ∧
    (boostVelocities b v).v3 - (boostVelocities b v).v2 = v.v3 - v.v2 ∧
    (boostVelocities b v).v1 - (boostVelocities b v).v3 = v.v1 - v.v3 := by
  constructor
  · ext i
    simp [boostVelocities]
  constructor
  · ext i
    simp [boostVelocities]
  · ext i
    simp [boostVelocities]

/-- A linear map preserving the Euclidean quadratic form is an orthogonal frame map. -/
def IsOrthogonal (Q : Vec3 →ₗ[ℝ] Vec3) : Prop :=
  ∀ r, normSq (Q r) = normSq r

lemma invCube_orthogonal (Q : Vec3 →ₗ[ℝ] Vec3) (hQ : IsOrthogonal Q) (r : Vec3) :
    invCube (Q r) = invCube r := by
  simp [invCube, hQ r]

def frameConfig (Q : Vec3 →ₗ[ℝ] Vec3) (a : Vec3) (x : Configuration) : Configuration :=
  ⟨Q x.x1 + a, Q x.x2 + a, Q x.x3 + a⟩

theorem sides_frame_covariant (Q : Vec3 →ₗ[ℝ] Vec3) (a : Vec3)
    (x : Configuration) :
    s1 (frameConfig Q a x) = Q (s1 x) ∧
    s2 (frameConfig Q a x) = Q (s2 x) ∧
    s3 (frameConfig Q a x) = Q (s3 x) := by
  constructor
  · simp [frameConfig, s1, map_sub]
  constructor
  · simp [frameConfig, s2, map_sub]
  · simp [frameConfig, s3, map_sub]

theorem sharedField_frame_covariant (Q : Vec3 →ₗ[ℝ] Vec3)
    (hQ : IsOrthogonal Q) (r1 r2 r3 : Vec3) :
    sharedField (Q r1) (Q r2) (Q r3) = Q (sharedField r1 r2 r3) := by
  simp [sharedField, invCube_orthogonal Q hQ, map_add, map_smul]

theorem relationalAcc1_frame_covariant (p : Parameters)
    (Q : Vec3 →ₗ[ℝ] Vec3) (a : Vec3) (hQ : IsOrthogonal Q)
    (x : Configuration) :
    relationalAcc1 p (s1 (frameConfig Q a x))
      (s2 (frameConfig Q a x)) (s3 (frameConfig Q a x)) =
    Q (relationalAcc1 p (s1 x) (s2 x) (s3 x)) := by
  rcases sides_frame_covariant Q a x with ⟨h1, h2, h3⟩
  rw [h1, h2, h3]
  simp [relationalAcc1, sharedField_frame_covariant Q hQ,
    invCube_orthogonal Q hQ, map_sub, map_smul]

/-! ## The dynamical phase state and its vector field -/

structure PhaseState where
  s1 : Vec3
  s2 : Vec3
  s3 : Vec3
  u1 : Vec3
  u2 : Vec3
  u3 : Vec3

/-- The position-side closure relation. -/
def PositionClosed (z : PhaseState) : Prop := z.s1 + z.s2 + z.s3 = 0

/-- The velocity-side closure relation. -/
def VelocityClosed (z : PhaseState) : Prop := z.u1 + z.u2 + z.u3 = 0

/-- Collision-free phase states. -/
def PhaseCollisionFree (z : PhaseState) : Prop :=
  0 < normSq z.s1 ∧ 0 < normSq z.s2 ∧ 0 < normSq z.s3

/-- The full first-order vector field `(u₁,u₂,u₃,A₁,A₂,A₃)`. -/
def gravitationalVectorField (p : Parameters) (z : PhaseState) : PhaseState :=
  ⟨z.u1, z.u2, z.u3,
   relationalAcc1 p z.s1 z.s2 z.s3,
   relationalAcc2 p z.s1 z.s2 z.s3,
   relationalAcc3 p z.s1 z.s2 z.s3⟩

theorem vectorField_preserves_tangent_closure (p : Parameters) (z : PhaseState)
    (hu : VelocityClosed z) :
    PositionClosed (gravitationalVectorField p z) ∧
    VelocityClosed (gravitationalVectorField p z) := by
  constructor
  · exact hu
  · exact relational_accelerations_close p z.s1 z.s2 z.s3

/-! ## Integral evolution as a self-consistent fixed point -/

/-- The Volterra evolution operator for the complete coupled state. -/
def evolutionOperator (p : Parameters) (z₀ : PhaseState)
    (z : ℝ → PhaseState) (t : ℝ) : PhaseState :=
  { s1 := z₀.s1 + ∫ τ in (0 : ℝ)..t, (z τ).u1
    s2 := z₀.s2 + ∫ τ in (0 : ℝ)..t, (z τ).u2
    s3 := z₀.s3 + ∫ τ in (0 : ℝ)..t, (z τ).u3
    u1 := z₀.u1 + ∫ τ in (0 : ℝ)..t,
      relationalAcc1 p (z τ).s1 (z τ).s2 (z τ).s3
    u2 := z₀.u2 + ∫ τ in (0 : ℝ)..t,
      relationalAcc2 p (z τ).s1 (z τ).s2 (z τ).s3
    u3 := z₀.u3 + ∫ τ in (0 : ℝ)..t,
      relationalAcc3 p (z τ).s1 (z τ).s2 (z τ).s3 }

/-- A history is an evolution fixed point when it equals its own Volterra image. -/
def IsIntegralFixedPoint (p : Parameters) (z₀ : PhaseState)
    (z : ℝ → PhaseState) : Prop :=
  ∀ t, z t = evolutionOperator p z₀ z t

/-- The integral fixed-point equation returns its prescribed initial state. -/
theorem integral_fixedpoint_initial (p : Parameters) (z₀ : PhaseState)
    (z : ℝ → PhaseState) (h : IsIntegralFixedPoint p z₀ z) :
    z 0 = z₀ := by
  simpa [IsIntegralFixedPoint, evolutionOperator] using h 0

/-- A periodic fixed-point history, without presuming that arbitrary initial data
are periodic. -/
def IsPeriodicHistory (z : ℝ → PhaseState) (T : ℝ) : Prop :=
  ∀ t, z (t + T) = z t

/-- A continuous polar-angle lift recording an integer winding of a nonzero
complex shape coordinate.  The representation is part of the certificate; it
is not inferred merely from periodicity. -/
structure WindingCertificate (q : ℝ → ℂ) (T : ℝ) where
  period_pos : 0 < T
  radius : ℝ → ℝ
  angle : ℝ → ℝ
  radius_pos : ∀ t, 0 < radius t
  lift : ∀ t, q t = (radius t : ℂ) * Complex.exp (Complex.I * (angle t : ℂ))
  turns : ∃ n : ℤ, angle T - angle 0 = 2 * Real.pi * n

/-- Componentwise continuity of a phase history. -/
def ContinuousHistory (z : ℝ → PhaseState) : Prop :=
  Continuous (fun t => (z t).s1) ∧
  Continuous (fun t => (z t).s2) ∧
  Continuous (fun t => (z t).s3) ∧
  Continuous (fun t => (z t).u1) ∧
  Continuous (fun t => (z t).u2) ∧
  Continuous (fun t => (z t).u3)

/-- The 8/9 organism packages the self-consistent physical history together
with its collision-free relational domain and regularity. -/
structure GravityOrganism89 (p : Parameters) (z₀ : PhaseState) where
  history : ℝ → PhaseState
  fixed_point : IsIntegralFixedPoint p z₀ history
  continuous_history : ContinuousHistory history
  positions_closed : ∀ t, PositionClosed (history t)
  velocities_closed : ∀ t, VelocityClosed (history t)
  collision_free : ∀ t, PhaseCollisionFree (history t)

/-- The defining equation of the organism is the full coupled integral law. -/
theorem organism89_integral_law (p : Parameters) (z₀ : PhaseState)
    (O : GravityOrganism89 p z₀) :
    ∀ t, O.history t = evolutionOperator p z₀ O.history t := O.fixed_point

/-- Initial data are recovered by the organism's own fixed-point history. -/
theorem organism89_initial_state (p : Parameters) (z₀ : PhaseState)
    (O : GravityOrganism89 p z₀) : O.history 0 = z₀ :=
  integral_fixedpoint_initial p z₀ O.history O.fixed_point

/-! ## Non-well-founded, nonterminal orbit hierarchy -/

def stableOp (S : Set ℤ) : Set ℤ :=
  {n | n - 1 ∈ S ∧ n + 1 ∈ S}

/-- Greatest post-fixed-point union for the two-sided integer orbit relation. -/
def Stable : Set ℤ := ⋃₀ {S : Set ℤ | S ⊆ stableOp S}

theorem stable_eq_univ : Stable = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro n
  unfold Stable
  apply Set.mem_sUnion.mpr
  refine ⟨Set.univ, ?_, Set.mem_univ n⟩
  intro k hk
  simp [stableOp]

theorem every_level_has_both_neighbors (n : ℤ) :
    n - 1 ∈ Stable ∧ n + 1 ∈ Stable := by
  rw [stable_eq_univ]
  simp

theorem no_terminal_orbit_level :
    (∀ n : ℤ, n ∈ Stable) ∧
    (∀ n : ℤ, n + 1 ∈ Stable) ∧
    (∀ n : ℤ, n - 1 ∈ Stable) := by
  rw [stable_eq_univ]
  simp

/-! ## Critical Lagrange-shape block and exceptional point -/

/-- The determinant of the reduced two-coordinate shape eigenvalue matrix. -/
def shapeDet (α₁ α₂ ω lam : ℂ) : ℂ :=
  (α₁ - lam ^ 2) * (α₂ - lam ^ 2) + 4 * ω ^ 2 * lam ^ 2

/-- Characteristic quartic of the reduced shape block. -/
def shapePolynomial (ω lam : ℂ) : ℂ :=
  lam ^ 4 + ω ^ 2 * lam ^ 2 + (ω ^ 4) / 4

theorem shapeDet_factorization (α₁ α₂ ω lam : ℂ)
    (hsum : α₁ + α₂ = 3 * ω ^ 2)
    (hprod : α₁ * α₂ = ω ^ 4 / 4) :
    shapeDet α₁ α₂ ω lam = (lam ^ 2 + ω ^ 2 / 2) ^ 2 := by
  unfold shapeDet
  calc
    (α₁ - lam ^ 2) * (α₂ - lam ^ 2) + 4 * ω ^ 2 * lam ^ 2
        = α₁ * α₂ - (α₁ + α₂) * lam ^ 2 + lam ^ 4 + 4 * ω ^ 2 * lam ^ 2 := by ring
    _ = (lam ^ 2 + ω ^ 2 / 2) ^ 2 := by rw [hsum, hprod]; ring

theorem shapeDet_eq_shapePolynomial (α₁ α₂ ω lam : ℂ)
    (hsum : α₁ + α₂ = 3 * ω ^ 2)
    (hprod : α₁ * α₂ = ω ^ 4 / 4) :
    shapeDet α₁ α₂ ω lam = shapePolynomial ω lam := by
  rw [shapeDet_factorization α₁ α₂ ω lam hsum hprod]
  unfold shapePolynomial
  ring

/-- The reduced matrix acts by the displayed two scalar equations. -/
def shapeKernelEquations (α₁ α₂ ω lam x y : ℂ) : Prop :=
  (α₁ - lam ^ 2) * x + (2 * ω * lam) * y = 0 ∧
  (-2 * ω * lam) * x + (α₂ - lam ^ 2) * y = 0

/-- The four-dimensional rotating-frame shape block used before eliminating
its velocity coordinates. Its rows encode the eigenvalue equation `A v = lam v`.
The coordinate order is `(x,y,p,q)`. -/
def shapeBlockAction (α₁ α₂ ω : ℂ) (v : Fin 4 → ℂ) : Fin 4 → ℂ := fun i =>
  if i = 0 then ω * v 1 + v 2
  else if i = 1 then -ω * v 0 + v 3
  else if i = 2 then (α₁ - ω ^ 2) * v 0 + ω * v 3
  else (α₂ - ω ^ 2) * v 1 - ω * v 2

/-- Reconstruction of the velocity coordinates from a shape eigenvector
`(x,y)`: `p = lamx - ωy`, `q = ωx + lamy`. -/
def shapeLift (ω lam x y : ℂ) : Fin 4 → ℂ := fun i =>
  if i = 0 then x
  else if i = 1 then y
  else if i = 2 then lam * x - ω * y
  else ω * x + lam * y

/-- The eliminated two-coordinate eigenproblem is equivalent to the full
four-coordinate eigenproblem on reconstructed vectors. -/
theorem shapeLift_eigen_iff (α₁ α₂ ω lam x y : ℂ) :
    shapeBlockAction α₁ α₂ ω (shapeLift ω lam x y) =
      lam • shapeLift ω lam x y ↔ shapeKernelEquations α₁ α₂ ω lam x y := by
  constructor
  · intro h
    have h2 := congrFun h (2 : Fin 4)
    have h3 := congrFun h (3 : Fin 4)
    constructor
    · change (α₁ - ω ^ 2) * x + ω * (ω * x + lam * y) =
        lam * (lam * x - ω * y) at h2
      linear_combination h2
    · change (α₂ - ω ^ 2) * y - ω * (lam * x - ω * y) =
        lam * (ω * x + lam * y) at h3
      linear_combination h3
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i
    · change ω * y + (lam * x - ω * y) = lam * x
      ring
    · change -ω * x + (ω * x + lam * y) = lam * y
      ring
    · change (α₁ - ω ^ 2) * x + ω * (ω * x + lam * y) =
        lam * (lam * x - ω * y)
      linear_combination h1
    · change (α₂ - ω ^ 2) * y - ω * (lam * x - ω * y) =
        lam * (ω * x + lam * y)
      linear_combination h2

/-- Every eigenvector of the full four-dimensional block is uniquely
reconstructed from its two shape coordinates. -/
theorem shapeBlock_eigenvector_reduction (α₁ α₂ ω lam : ℂ)
    (v : Fin 4 → ℂ)
    (h : shapeBlockAction α₁ α₂ ω v = lam • v) :
    v = shapeLift ω lam (v 0) (v 1) ∧
      shapeKernelEquations α₁ α₂ ω lam (v 0) (v 1) := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have hp : v 2 = lam * v 0 - ω * v 1 := by
    change ω * v 1 + v 2 = lam * v 0 at h0
    linear_combination h0
  have hq : v 3 = ω * v 0 + lam * v 1 := by
    change -ω * v 0 + v 3 = lam * v 1 at h1
    linear_combination h1
  have hv : v = shapeLift ω lam (v 0) (v 1) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change v 2 = lam * v 0 - ω * v 1
      exact hp
    · change v 3 = ω * v 0 + lam * v 1
      exact hq
  have hLift : shapeBlockAction α₁ α₂ ω
      (shapeLift ω lam (v 0) (v 1)) =
      lam • shapeLift ω lam (v 0) (v 1) := by
    rw [← hv]
    exact h
  exact ⟨hv, (shapeLift_eigen_iff α₁ α₂ ω lam (v 0) (v 1)).mp hLift⟩

/-- At a singular two-by-two block with a nonzero off-diagonal entry, its
kernel is exactly one-dimensional: every vector is a scalar multiple of
`(b,-a)`. -/
theorem two_by_two_kernel_is_line (a b c d x y : ℂ)
    (hb : b ≠ 0) (hdet : a * d - b * c = 0) :
    (a * x + b * y = 0 ∧ c * x + d * y = 0) ↔
      ∃ t : ℂ, x = t * b ∧ y = -(t * a) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨x / b, ?_, ?_⟩
    · field_simp [hb] <;> ring
    · calc
        y = -(a * x) / b := by
          field_simp [hb]
          linear_combination h₁
        _ = -((x / b) * a) := by ring
  · rintro ⟨t, rfl, rfl⟩
    constructor
    · ring
    · calc
        c * (t * b) + d * (-(t * a)) = t * (c * b - d * a) := by ring
        _ = 0 := by
          have h' : c * b - d * a = 0 := by linear_combination -hdet
          rw [h']
          simp

/-- Critical spectral degeneracy plus a nonzero coupling entry. -/
def IsExceptionalShapePoint (α₁ α₂ ω lam : ℂ) : Prop :=
  shapeDet α₁ α₂ ω lam = 0 ∧ 2 * ω * lam ≠ 0

theorem critical_shape_is_exceptional (α₁ α₂ ω lam : ℂ)
    (hsum : α₁ + α₂ = 3 * ω ^ 2)
    (hprod : α₁ * α₂ = ω ^ 4 / 4)
    (hroot : lam ^ 2 + ω ^ 2 / 2 = 0)
    (hωlam : ω * lam ≠ 0) :
    IsExceptionalShapePoint α₁ α₂ ω lam ∧
    (∀ x y : ℂ,
      shapeKernelEquations α₁ α₂ ω lam x y ↔
        ∃ t : ℂ, x = t * (2 * ω * lam) ∧
          y = -(t * (α₁ - lam ^ 2))) := by
  have hdet0 : shapeDet α₁ α₂ ω lam = 0 := by
    rw [shapeDet_factorization α₁ α₂ ω lam hsum hprod]
    rw [hroot]
    norm_num
  have hω : ω ≠ 0 := by
    intro hzero
    apply hωlam
    rw [hzero]
    simp
  have hlam : lam ≠ 0 := by
    intro hzero
    apply hωlam
    rw [hzero]
    simp
  have hb : 2 * ω * lam ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hω) hlam
  have hdet : (α₁ - lam ^ 2) * (α₂ - lam ^ 2) -
      (2 * ω * lam) * (-2 * ω * lam) = 0 := by
    calc
      (α₁ - lam ^ 2) * (α₂ - lam ^ 2) -
          (2 * ω * lam) * (-2 * ω * lam) = shapeDet α₁ α₂ ω lam := by
            unfold shapeDet
            ring
      _ = 0 := hdet0
  constructor
  · exact ⟨hdet0, hb⟩
  · intro x y
    exact two_by_two_kernel_is_line
      (α₁ - lam ^ 2) (2 * ω * lam) (-2 * ω * lam) (α₂ - lam ^ 2) x y hb hdet

/-- The eigenspace of the full four-dimensional shape block is one-dimensional
at the exceptional point. This upgrades the reduced two-coordinate kernel
calculation to the complete rotating-frame shape block. -/
theorem critical_full_shape_block_kernel_line (α₁ α₂ ω lam : ℂ)
    (hsum : α₁ + α₂ = 3 * ω ^ 2)
    (hprod : α₁ * α₂ = ω ^ 4 / 4)
    (hroot : lam ^ 2 + ω ^ 2 / 2 = 0)
    (hωlam : ω * lam ≠ 0)
    (v : Fin 4 → ℂ)
    (hv : shapeBlockAction α₁ α₂ ω v = lam • v) :
    ∃ t : ℂ,
      v = t • shapeLift ω lam (2 * ω * lam) (-(α₁ - lam ^ 2)) := by
  have hdet0 : shapeDet α₁ α₂ ω lam = 0 := by
    rw [shapeDet_factorization α₁ α₂ ω lam hsum hprod]
    rw [hroot]
    norm_num
  have hdet : (α₁ - lam ^ 2) * (α₂ - lam ^ 2) -
      (2 * ω * lam) * (-2 * ω * lam) = 0 := by
    calc
      (α₁ - lam ^ 2) * (α₂ - lam ^ 2) -
          (2 * ω * lam) * (-2 * ω * lam) = shapeDet α₁ α₂ ω lam := by
            unfold shapeDet
            ring
      _ = 0 := hdet0
  have hω : ω ≠ 0 := by
    intro hzero
    apply hωlam
    rw [hzero]
    simp
  have hlam : lam ≠ 0 := by
    intro hzero
    apply hωlam
    rw [hzero]
    simp
  have hb : 2 * ω * lam ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hω) hlam
  rcases shapeBlock_eigenvector_reduction α₁ α₂ ω lam v hv with ⟨hvec, hkernel⟩
  have hline := (two_by_two_kernel_is_line
    (α₁ - lam ^ 2) (2 * ω * lam) (-2 * ω * lam) (α₂ - lam ^ 2)
    (v 0) (v 1) hb hdet).mp hkernel
  rcases hline with ⟨t, hx, hy⟩
  refine ⟨t, ?_⟩
  rw [hvec, hx, hy]
  ext i
  fin_cases i <;> simp [shapeLift] <;> ring

/-- The two critical shape coefficients associated with the Gascheau parameter
at its exceptional value. -/
def alphaPlus (ω : ℝ) : ℝ := (3 / 2 + Real.sqrt 2) * ω ^ 2

def alphaMinus (ω : ℝ) : ℝ := (3 / 2 - Real.sqrt 2) * ω ^ 2

theorem alphaPlus_add_alphaMinus (ω : ℝ) :
    alphaPlus ω + alphaMinus ω = 3 * ω ^ 2 := by
  simp [alphaPlus, alphaMinus]
  ring

theorem alphaPlus_mul_alphaMinus (ω : ℝ) :
    alphaPlus ω * alphaMinus ω = ω ^ 4 / 4 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoeff : (3 / 2 + Real.sqrt 2) * (3 / 2 - Real.sqrt 2) = (1 / 4 : ℝ) := by
    nlinarith [hs]
  unfold alphaPlus alphaMinus
  calc
    ((3 / 2 + Real.sqrt 2) * ω ^ 2) *
        ((3 / 2 - Real.sqrt 2) * ω ^ 2) =
        ((3 / 2 + Real.sqrt 2) * (3 / 2 - Real.sqrt 2)) * ω ^ 4 := by ring
    _ = ω ^ 4 / 4 := by rw [hcoeff]; ring

/-- Exact positive-mass critical example: `(m₁,m₂,m₃)=(1,1,25+18√2)`.
It satisfies `M² = 27 σ₂`, hence `27 σ₂ / M² = 1`. -/
theorem exact_critical_mass_identity :
    (27 + 18 * Real.sqrt 2) ^ 2 =
      27 * (51 + 36 * Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [hs]

/-- Gascheau's dimensionless mass parameter. -/
def gascheauParameter (p : Parameters) : ℝ :=
  27 * p.sigma₂ / (p.totalMass ^ 2)

/-- The positive-mass critical example used to instantiate the exceptional
shape condition. -/
def exactCriticalParameters : Parameters where
  G := 1
  m1 := 1
  m2 := 1
  m3 := 25 + 18 * Real.sqrt 2
  hG := by norm_num
  hm1 := by norm_num
  hm2 := by norm_num
  hm3 := by have h := Real.sqrt_nonneg (2 : ℝ); linarith

theorem exact_critical_parameters_beta :
    gascheauParameter exactCriticalParameters = 1 := by
  have hmass := exact_critical_mass_identity
  have hden : 27 * (51 + 36 * Real.sqrt 2) ≠ 0 := by
    positivity
  unfold gascheauParameter Parameters.sigma₂ Parameters.totalMass exactCriticalParameters
  have hnum : 1 * 1 + 1 * (25 + 18 * Real.sqrt 2) +
      (25 + 18 * Real.sqrt 2) * 1 = 51 + 36 * Real.sqrt 2 := by ring
  have htot : 1 + 1 + (25 + 18 * Real.sqrt 2) = 27 + 18 * Real.sqrt 2 := by ring
  rw [hnum, htot, hmass]
  field_simp [hden]

/-- Complex coordinate of one oriented side; used to carry an actual angle
lift for a planar projection of the relational orbit. -/
def shapeCoordinate (z : PhaseState) : ℂ :=
  (z.s1 0 : ℂ) + Complex.I * (z.s1 1 : ℂ)

/-- The integrated 8/9 object: one collision-free gravitational history is
simultaneously its own integral fixed point (8), carries a periodic winding
lift, and has the critical exceptional shape block (9). -/
structure ExceptionalWindingOrganism89 (p : Parameters) (z₀ : PhaseState) where
  organism : GravityOrganism89 p z₀
  period : ℝ
  periodic : IsPeriodicHistory organism.history period
  winding : WindingCertificate (fun t => shapeCoordinate (organism.history t)) period
  omega : ℝ
  omega_pos : 0 < omega
  lambda : ℂ
  critical_root : lambda ^ 2 + (omega : ℂ) ^ 2 / 2 = 0
  nonzero_coupling : (omega : ℂ) * lambda ≠ 0
  critical_mass_parameter : gascheauParameter p = 1

/-- The exceptional spectral structure is a theorem about the very same
fixed-point/winding organism, not a second physical system. -/
theorem exceptional_winding_organism_has_EP
    (p : Parameters) (z₀ : PhaseState)
    (O : ExceptionalWindingOrganism89 p z₀) :
    gascheauParameter p = 1 ∧
    IsExceptionalShapePoint (alphaPlus O.omega : ℂ)
      (alphaMinus O.omega : ℂ) (O.omega : ℂ) O.lambda ∧
    (∀ x y : ℂ,
      shapeKernelEquations (alphaPlus O.omega : ℂ)
        (alphaMinus O.omega : ℂ) (O.omega : ℂ) O.lambda x y ↔
      ∃ t : ℂ, x = t * (2 * (O.omega : ℂ) * O.lambda) ∧
        y = -(t * ((alphaPlus O.omega : ℂ) - O.lambda ^ 2))) ∧
    (∀ v : Fin 4 → ℂ,
      shapeBlockAction (alphaPlus O.omega : ℂ)
        (alphaMinus O.omega : ℂ) (O.omega : ℂ) v = O.lambda • v →
      ∃ t : ℂ, v = t • shapeLift (O.omega : ℂ) O.lambda
        (2 * (O.omega : ℂ) * O.lambda)
        (-((alphaPlus O.omega : ℂ) - O.lambda ^ 2))) := by
  have hsumR := alphaPlus_add_alphaMinus O.omega
  have hprodR := alphaPlus_mul_alphaMinus O.omega
  have hsum : (alphaPlus O.omega : ℂ) + (alphaMinus O.omega : ℂ) =
      3 * (O.omega : ℂ) ^ 2 := by exact_mod_cast hsumR
  have hprod : (alphaPlus O.omega : ℂ) * (alphaMinus O.omega : ℂ) =
      (O.omega : ℂ) ^ 4 / 4 := by exact_mod_cast hprodR
  have hred := critical_shape_is_exceptional
    (alphaPlus O.omega : ℂ) (alphaMinus O.omega : ℂ)
    (O.omega : ℂ) O.lambda hsum hprod O.critical_root O.nonzero_coupling
  refine ⟨O.critical_mass_parameter, hred.1, hred.2, ?_⟩
  intro v hv
  exact critical_full_shape_block_kernel_line
    (alphaPlus O.omega : ℂ) (alphaMinus O.omega : ℂ)
    (O.omega : ℂ) O.lambda hsum hprod O.critical_root
    O.nonzero_coupling v hv

/-! ## Integrated theorem package -/

/-- The relational Newtonian organism's instantaneous physical identities.
The three relational accelerations are the differences of the Newtonian body
accelerations; their closure, momentum-rate cancellation, torque-rate
cancellation, and energy-rate cancellation all hold in the same state. -/
theorem gravitational_organism_instantaneous_laws
    (p : Parameters) (x : Configuration) (v : Velocities) :
    relationalAcc1 p (s1 x) (s2 x) (s3 x) = bodyAcc3 p x - bodyAcc2 p x ∧
    relationalAcc2 p (s1 x) (s2 x) (s3 x) = bodyAcc1 p x - bodyAcc3 p x ∧
    relationalAcc3 p (s1 x) (s2 x) (s3 x) = bodyAcc2 p x - bodyAcc1 p x ∧
    relationalAcc1 p (s1 x) (s2 x) (s3 x) +
      relationalAcc2 p (s1 x) (s2 x) (s3 x) +
      relationalAcc3 p (s1 x) (s2 x) (s3 x) = 0 ∧
    momentumRate p x = 0 ∧
    torqueRate p x = 0 ∧
    kineticPower p x v + potentialEnergyDirectionalRate p x v = 0 := by
  exact ⟨relationalAcc1_eq_body p x,
    relationalAcc2_eq_body p x,
    relationalAcc3_eq_body p x,
    relational_accelerations_close p (s1 x) (s2 x) (s3 x),
    momentum_rate_zero p x,
    torque_rate_zero p x,
    energy_rate_zero p x v⟩

end Imscribing.ThreeBody