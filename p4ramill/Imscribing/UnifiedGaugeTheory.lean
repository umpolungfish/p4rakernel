import Mathlib

/-!
# A unified formal skeleton for the extracted mathematical physics

Extracted from the table (right-hand column) and fused into one development:

| table fragment                                   | where it lives below                    |
|--------------------------------------------------|-----------------------------------------|
| `A_μ ∈ Ω¹(M,𝔤)`, `U_μ ∈ G`, `(A_i,E_i) ∈ T*𝒜`   | §1 `PhasePoint`, §2 link variables      |
| `F_μν`, `D_μ`, `D_μ F^μν = 0`                    | §3 Yang–Mills                           |
| `{f,g}`, `[Aᵢᵃ,Eⱼᵇ] = iℏδδδ`, `[Q_a,Q_b]=f Q_c`  | §4 Poisson / CCR / gauge algebra        |
| `d⟨O⟩/dt = (i/ℏ)⟨[H,O]⟩`, conservation           | §5 `QuantumGaugeSystem`                 |
| `Z(β)`, `ρ_β`, gap `spec H ∩ (0,Δ) = ∅`, `C(t)` | §6 thermal / spectral                   |
| `Θ² = id`, `⟨(ΘF)F⟩ ≥ 0`                         | §5 reflection positivity                |
| `U_μν`, `W_p`, `S_W`, `W_R(C)`                   | §2 Wilson loops / action                |
| `∮A = nπ, n ∈ ℤ₂`, `dim H_phys = 1`             | §7                                      |
| catalog: `embed (reflectConj γ) = revFlip (embed γ)` | §8                                  |

Interpretive choices are tagged `NOTE`.  NOT compiled; Mathlib API names may need small fixes.
-/

open Filter

namespace UnifiedGaugeTheory

/-! ## §1 Phase space `T*𝒜` -/

/-- NOTE: `T*𝒜 ≅ 𝒜 × 𝒜*`, with `𝔤* ≅ 𝔤` via the Killing form; points are pairs `(A, E)`. -/
abbrev PhasePoint (κ : Type*) (𝔤 : Type*) := (κ → 𝔤) × (κ → 𝔤)

/-! ## §2 Lattice gauge theory: links, plaquettes, Wilson loops, Wilson action -/

section Lattice

variable {G : Type*} [Group G] {Link : Type*}

/-- Plaquette holonomy `U_μν = U_μ U_ν U_μ† U_ν†` (dagger = inverse in a group). -/
def plaquette (Uμ Uν : G) : G := Uμ * Uν * Uμ⁻¹ * Uν⁻¹

/-- An oriented step: `(ℓ, true)` traverses `ℓ` forwards, `(ℓ, false)` backwards. -/
abbrev Step (Link : Type*) := Link × Bool

def step (U : Link → G) : Step Link → G
  | (l, true) => U l
  | (l, false) => (U l)⁻¹

def flipStep (s : Step Link) : Step Link := (s.1, !s.2)

/-- Ordered product of link variables along a path (lattice `𝒫 exp(ig∮A)`). -/
def pathHol (U : Link → G) (p : List (Step Link)) : G := (p.map (step U)).prod

/-- Reversed path. -/
def revPath (p : List (Step Link)) : List (Step Link) := (p.map flipStep).reverse

theorem pathHol_append (U : Link → G) (p q : List (Step Link)) :
    pathHol U (p ++ q) = pathHol U p * pathHol U q := by
  simp [pathHol, List.map_append, List.prod_append]

/-- Reversing a path inverts its holonomy. -/
theorem pathHol_rev (U : Link → G) (p : List (Step Link)) :
    pathHol U (revPath p) = (pathHol U p)⁻¹ := by
  induction p with
  | nil => simp [pathHol, revPath]
  | cons a p ih =>
    have h : revPath (a :: p) = revPath p ++ [flipStep a] := by simp [revPath]
    rw [h, pathHol_append, ih]
    obtain ⟨l, b⟩ := a
    cases b <;> simp [pathHol, step, flipStep, mul_inv_rev]

/-- Wilson loop in a matrix representation: `W_R(C) = d_R⁻¹ Tr_R 𝒫(…)`. -/
noncomputable def wilsonLoop {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (U : Link → G) (C : List (Step Link)) : ℂ :=
  ((n : ℂ)⁻¹) * Matrix.trace (ρ (pathHol U C))

/-- For a unitary representation, reversing a loop conjugates the Wilson loop
(`W_R(C̄) = conj W_R(C)`): the lattice form of reflect-conjugation = reversal. -/
theorem wilsonLoop_rev {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ g, ρ g⁻¹ = (ρ g)ᴴ) (U : Link → G) (C : List (Step Link)) :
    wilsonLoop ρ U (revPath C) = star (wilsonLoop ρ U C) := by
  unfold wilsonLoop
  rw [pathHol_rev, hU, Matrix.trace_conjTranspose, star_mul', star_inv₀]
  simp [mul_comm]

/-- Plaquette observable `W_p = d_R⁻¹ Re Tr_R U_μν`. -/
noncomputable def wilsonPlaquette {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (Uμ Uν : G) : ℝ :=
  ((n : ℝ)⁻¹) * (Matrix.trace (ρ (plaquette Uμ Uν))).re

/-- Wilson action `S_W = β Σ_p (1 − W_p)`. -/
noncomputable def wilsonAction {n : ℕ} {P : Type*} [Fintype P]
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (β : ℝ) (plaq : P → G × G) : ℝ :=
  β * ∑ p, (1 - wilsonPlaquette ρ (plaq p).1 (plaq p).2)

end Lattice

/-! ## §3 Continuum Yang–Mills: `F_μν`, `D_μ`, `D_μ F^μν = 0` -/

section YangMills

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [Module ℂ 𝔤] [Bracket 𝔤 𝔤]

/-- Partial derivative `∂_μ` on fields over `ℝ⁴`. -/
noncomputable def pd (μ : Fin 4) (f : (Fin 4 → ℝ) → 𝔤) (x : Fin 4 → ℝ) : 𝔤 :=
  deriv (fun s : ℝ => f (Function.update x μ s)) (x μ)

/-- `F_μν = ∂_μ A_ν − ∂_ν A_μ + i g [A_μ, A_ν]`. -/
noncomputable def fieldStrength (A : Fin 4 → (Fin 4 → ℝ) → 𝔤) (g : ℝ)
    (μ ν : Fin 4) (x : Fin 4 → ℝ) : 𝔤 :=
  pd μ (A ν) x - pd ν (A μ) x + (Complex.I * (g : ℂ)) • ⁅A μ x, A ν x⁆

/-- Adjoint covariant derivative `D_μ Φ = ∂_μ Φ + i g [A_μ, Φ]`. -/
noncomputable def covDeriv (A : Fin 4 → (Fin 4 → ℝ) → 𝔤) (g : ℝ)
    (μ : Fin 4) (Φ : (Fin 4 → ℝ) → 𝔤) (x : Fin 4 → ℝ) : 𝔤 :=
  pd μ Φ x + (Complex.I * (g : ℂ)) • ⁅A μ x, Φ x⁆

/-- Yang–Mills equation `D_μ F^μν = 0`.  NOTE: diagonal metric `η`, `F^μν = η_μ η_ν F_μν`. -/
def YangMills (A : Fin 4 → (Fin 4 → ℝ) → 𝔤) (g : ℝ) (η : Fin 4 → ℝ) : Prop :=
  ∀ (ν : Fin 4) (x : Fin 4 → ℝ),
    ∑ μ, covDeriv A g μ (fun y => (η μ * η ν) • fieldStrength A g μ ν y) x = 0

/-- `F_μν = −F_νμ` when the bracket is antisymmetric. -/
theorem fieldStrength_antisymm (A : Fin 4 → (Fin 4 → ℝ) → 𝔤) (g : ℝ)
    (hanti : ∀ a b : 𝔤, ⁅a, b⁆ = -⁅b, a⁆) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    fieldStrength A g μ ν x = - fieldStrength A g ν μ x := by
  simp only [fieldStrength]
  rw [hanti (A μ x) (A ν x), smul_neg]
  abel

end YangMills

/-! ## §4 Poisson bracket, canonical commutation, gauge algebra -/

section Algebra

/-- `{f,g} = ∂_q f ∂_p g − ∂_p f ∂_q g` on `ℝ × ℝ`. -/
noncomputable def poissonBracket (f g : ℝ × ℝ → ℝ) (q p : ℝ) : ℝ :=
  deriv (fun s => f (s, p)) q * deriv (fun s => g (q, s)) p
    - deriv (fun s => f (q, s)) p * deriv (fun s => g (s, p)) q

theorem poisson_q_p (q p : ℝ) : poissonBracket Prod.fst Prod.snd q p = 1 := by
  simp [poissonBracket]

/-- Gauge Lie algebra `[Q_a, Q_b] = f_ab^c Q_c`. -/
def GaugeLieRelation {𝔄 : Type*} [Ring 𝔄] {ι : Type*} [Fintype ι]
    (Q : ι → 𝔄) (f : ι → ι → ι → ℤ) : Prop :=
  ∀ a b, Q a * Q b - Q b * Q a = ∑ c, (f a b c) • Q c

/-- Dirac quantization: `[Q f, Q g] = iℏ Q {f,g}`. -/
def Quantization {𝔄 : Type*} [Ring 𝔄] [Algebra ℂ 𝔄] (ħ : ℝ)
    (Q : (ℝ × ℝ → ℝ) → 𝔄) : Prop :=
  ∀ f g, Q f * Q g - Q g * Q f
    = (Complex.I * (ħ : ℂ)) • Q (fun z => poissonBracket f g z.1 z.2)

end Algebra

/-! ## §5 The unified quantum gauge system -/

/-- Everything the right-hand column asserts, in one structure over a ℂ-algebra `𝔄`
of observables.  Index `κ` collects `(site, direction, colour)` labels, so
`δᵃᵇ δᵢⱼ δ³(x−y)` becomes the Kronecker delta on `κ` (NOTE: lattice regularization). -/
structure QuantumGaugeSystem (κ : Type*) (𝔄 : Type*)
    [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄] where
  ħ : ℝ
  ħ_pos : 0 < ħ
  A : κ → 𝔄
  E : κ → 𝔄
  /-- `[Aₖ, Eₗ] = iℏ δₖₗ` -/
  ccr : ∀ k l, A k * E l - E l * A k
          = (if k = l then Complex.I * (ħ : ℂ) else 0) • (1 : 𝔄)
  AA : ∀ k l, A k * A l = A l * A k
  EE : ∀ k l, E k * E l = E l * E k
  /-- Hamiltonian. -/
  H : 𝔄
  /-- State (expectation functional), normalized. -/
  ω : 𝔄 →ₗ[ℂ] ℂ
  ω_one : ω 1 = 1
  /-- Reflection `Θ`, an involution. -/
  Θ : 𝔄 → 𝔄
  Θ_invol : ∀ F, Θ (Θ F) = F
  /-- Reflection positivity `⟨(ΘF) F⟩ ≥ 0`. -/
  refl_pos : ∀ F, (ω (Θ F * F)).im = 0 ∧ 0 ≤ (ω (Θ F * F)).re

namespace QuantumGaugeSystem

variable {κ 𝔄 : Type*} [DecidableEq κ] [Ring 𝔄] [Algebra ℂ 𝔄]
variable (S : QuantumGaugeSystem κ 𝔄)

theorem ccr_diag (k : κ) :
    S.A k * S.E k - S.E k * S.A k = (Complex.I * (S.ħ : ℂ)) • (1 : 𝔄) := by
  simpa using S.ccr k k

theorem ccr_offdiag {k l : κ} (h : k ≠ l) :
    S.A k * S.E l = S.E l * S.A k := by
  have := S.ccr k l
  rw [if_neg h, zero_smul] at this
  exact sub_eq_zero.mp this

/-- `Θ` is injective (because `Θ² = id`). -/
theorem Θ_injective : Function.Injective S.Θ := by
  intro a b h
  have := congrArg S.Θ h
  rwa [S.Θ_invol, S.Θ_invol] at this

/-- Heisenberg equation `d⟨O⟩/dt = (i/ℏ) ⟨[H,O]⟩` for an expectation curve `e`. -/
def Heisenberg (O : 𝔄) (e : ℝ → ℂ) : Prop :=
  ∀ t, HasDerivAt e (Complex.I / (S.ħ : ℂ) * S.ω (S.H * O - O * S.H)) t

/-- `[H,O] = 0 ⇒ ⟨O⟩` is conserved. -/
theorem conserved_of_commute {O : 𝔄} {e : ℝ → ℂ}
    (hder : S.Heisenberg O e) (hc : S.H * O = O * S.H) :
    ∀ t, deriv e t = 0 := by
  intro t
  rw [(hder t).deriv, hc, sub_self, map_zero, mul_zero]

end QuantumGaugeSystem

/-! ## §6 Thermal and spectral structure (finite spectrum model) -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Z(β) = Tr e^{−βH}` in the eigenbasis with energies `E`. -/
noncomputable def Z (E : ι → ℝ) (β : ℝ) : ℝ := ∑ n, Real.exp (-β * E n)

/-- Diagonal of `ρ_β = Z⁻¹ e^{−βH}`. -/
noncomputable def gibbs (E : ι → ℝ) (β : ℝ) (n : ι) : ℝ := Real.exp (-β * E n) / Z E β

theorem Z_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) : 0 < Z E β :=
  Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- `Tr ρ_β = 1`. -/
theorem gibbs_sum_one [Nonempty ι] (E : ι → ℝ) (β : ℝ) : ∑ n, gibbs E β n = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (Z_pos E β).ne'

/-- Mass gap: `spec H ∩ (0, Δ) = ∅`, `Δ > 0`. -/
def MassGap (spec : Set ℝ) (Δ : ℝ) : Prop := 0 < Δ ∧ spec ∩ Set.Ioo 0 Δ = ∅

/-- Spectral representation `C(t) = Σ_{n≠0} |⟨0|O|n⟩|² e^{−(Eₙ−E₀)t}`. -/
noncomputable def correlator (E : ι → ℝ) (a : ι → ℂ) (n₀ : ι) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.univ.erase n₀, ‖a n‖ ^ 2 * Real.exp (-(E n - E n₀) * t)

/-- Gap ⇒ exponential clustering: `C(t) ≤ (Σ|aₙ|²) e^{−Δt}` for `t ≥ 0`. -/
theorem correlator_le (E : ι → ℝ) (a : ι → ℂ) (n₀ : ι) (Δ : ℝ)
    (hgap : ∀ n, n ≠ n₀ → Δ ≤ E n - E n₀) {t : ℝ} (ht : 0 ≤ t) :
    correlator E a n₀ t ≤ (∑ n ∈ Finset.univ.erase n₀, ‖a n‖ ^ 2) * Real.exp (-Δ * t) := by
  unfold correlator
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hne : n ≠ n₀ := Finset.ne_of_mem_erase hn
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (hgap n hne) ht
  linarith

/-- `C(t) = O(e^{−Δ t})` as an asymptotic statement. -/
def ExpDecay (C : ℝ → ℝ) (Δ : ℝ) : Prop :=
  C =O[atTop] fun t => Real.exp (-Δ * t)

end Spectral

/-! ## §7 `ℤ₂` holonomy quantization and the one-dimensional physical space -/

/-- `∮_γ A = nπ` with `n ∈ ℤ₂` (loop integral abstracted to the real number `hol`). -/
def Z2Holonomy (hol : ℝ) : Prop := ∃ n : ZMod 2, hol = (n.val : ℝ) * Real.pi

/-- `dim H_phys = 1`. -/
def PhysDimOne (Hphys : Type*) [AddCommGroup Hphys] [Module ℂ Hphys] : Prop :=
  Module.finrank ℂ Hphys = 1

/-! ## §8 Catalog semantics -/

/-- “The reflect-conjugate loop embedded into the torus is the reverse of the original
embedded loop”: `embedLoop4DZ L (reflectConjLoop4DZ γ) = revFlip (embedLoop4DZ L γ)`. -/
def CatalogReflectConj
    (Loop4DZ : Type*) (Torus : ℕ → Type*)
    (embedLoop4DZ : (L : ℕ) → Loop4DZ → Torus L)
    (reflectConjLoop4DZ : Loop4DZ → Loop4DZ)
    (revFlip : (L : ℕ) → Torus L → Torus L) : Prop :=
  ∀ (L : ℕ) (γ : Loop4DZ),
    embedLoop4DZ L (reflectConjLoop4DZ γ) = revFlip L (embedLoop4DZ L γ)

/-- Concrete instance on lattice paths: reflecting links by `r` (an involution on links)
then reversing is compatible with `pathHol` — the Wilson-loop-level meaning of the catalog
statement (`Θ` acts on `W(C)` as `W(C̄)`). -/
theorem reflectConj_hol {G : Type*} [Group G] {Link : Type*}
    (U : Link → G) (r : Link → Link) (p : List (Step Link)) :
    pathHol U (revPath (p.map fun s => (r s.1, s.2)))
      = (pathHol U (p.map fun s => (r s.1, s.2)))⁻¹ :=
  pathHol_rev U _

end UnifiedGaugeTheory
