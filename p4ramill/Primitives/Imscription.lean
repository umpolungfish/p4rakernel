-- Imscribing/Primitives/Imscription.lean
-- Imscription struct, primitive distance (Hamming + ordinal), and key encodings.
-- Proves P-70 (Higgs = axion = inflaton) by rfl.
-- All primitive names are canonical (v0.5.69).

import Imscribing.Primitives.Core

namespace Imscribing.Primitives

open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- IMSCRIPTION STRUCT
-- An Imscription is a 12-tuple ⟨D; T; R; P; F; K; G; Γ; Φ; H; S; Ω⟩.
-- Field name 'rel' used for Relational (R) since 'rec' is reserved in Lean 4.
-- @[ext] generates Imscription.ext for pointwise equality.
-- ============================================================

@[ext]
structure Imscription : Type where
  dim   : Dimensionality   -- D
  top   : Topology         -- T
  rel   : Relational       -- R
  pol   : Polarity         -- P
  fid   : Fidelity         -- F
  kin   : KineticChar      -- K
  gran  : Granularity      -- G
  gram  : Grammar          -- Γ
  crit  : Criticality      -- Φ
  chir  : Chirality        -- H
  stoi  : Stoichiometry    -- S
  prot  : Protection       -- Ω
  deriving DecidableEq, Repr

-- ============================================================
-- HAMMING DISTANCE
-- Count of component mismatches. Zero iff tuples are identical.
-- ============================================================

def primitiveMismatches (a b : Imscription) : Nat :=
  (if a.dim  = b.dim  then 0 else 1) +
  (if a.top  = b.top  then 0 else 1) +
  (if a.rel  = b.rel  then 0 else 1) +
  (if a.pol  = b.pol  then 0 else 1) +
  (if a.fid  = b.fid  then 0 else 1) +
  (if a.kin  = b.kin  then 0 else 1) +
  (if a.gran = b.gran then 0 else 1) +
  (if a.gram = b.gram then 0 else 1) +
  (if a.crit = b.crit then 0 else 1) +
  (if a.chir = b.chir then 0 else 1) +
  (if a.stoi = b.stoi then 0 else 1) +
  (if a.prot = b.prot then 0 else 1)

theorem primitiveMismatches_self (a : Imscription) : primitiveMismatches a a = 0 := by
  simp [primitiveMismatches]

theorem primitiveMismatches_symm (a b : Imscription) :
    primitiveMismatches a b = primitiveMismatches b a := by
  simp only [primitiveMismatches, eq_comm]

private lemma ite_mismatch_le_one (p : Prop) [Decidable p] :
    (if p then 0 else 1) ≤ 1 := by split_ifs <;> omega

theorem primitiveMismatches_le_12 (a b : Imscription) :
    primitiveMismatches a b ≤ 12 := by
  unfold primitiveMismatches
  have h1  := ite_mismatch_le_one (a.dim  = b.dim)
  have h2  := ite_mismatch_le_one (a.top  = b.top)
  have h3  := ite_mismatch_le_one (a.rel  = b.rel)
  have h4  := ite_mismatch_le_one (a.pol  = b.pol)
  have h5  := ite_mismatch_le_one (a.fid  = b.fid)
  have h6  := ite_mismatch_le_one (a.kin  = b.kin)
  have h7  := ite_mismatch_le_one (a.gran = b.gran)
  have h8  := ite_mismatch_le_one (a.gram = b.gram)
  have h9  := ite_mismatch_le_one (a.crit = b.crit)
  have h10 := ite_mismatch_le_one (a.chir = b.chir)
  have h11 := ite_mismatch_le_one (a.stoi = b.stoi)
  have h12 := ite_mismatch_le_one (a.prot = b.prot)
  omega

theorem primitiveMismatches_zero_iff (a b : Imscription) :
    primitiveMismatches a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold primitiveMismatches at h
    ext
    all_goals {
      by_contra hne
      have hterm : (if _ = _ then 0 else 1) = 1 := if_neg hne
      simp only [hterm] at h; omega
    }
  · rintro rfl; exact primitiveMismatches_self a

-- ============================================================
-- TENSOR PRODUCT (structural composition)
-- Union primitives: max (D, T, R, G, Γ, Φ, H, S, Ω)
-- Bottleneck primitives: min (P, F) — weaker partner wins
-- ============================================================

def tensorProduct (a b : Imscription) : Imscription := {
  dim  := if compare a.dim  b.dim  = .lt then b.dim  else a.dim   -- max
  top  := if compare a.top  b.top  = .lt then b.top  else a.top   -- max
  rel  := if compare a.rel  b.rel  = .lt then b.rel  else a.rel   -- max
  pol  := if compare a.pol  b.pol  = .lt then a.pol  else b.pol   -- min (bottleneck)
  fid  := if compare a.fid  b.fid  = .lt then a.fid  else b.fid   -- min (bottleneck)
  kin  := if compare a.kin  b.kin  = .lt then b.kin  else a.kin   -- max
  gran := if compare a.gran b.gran = .lt then b.gran else a.gran   -- max
  gram := if compare a.gram b.gram = .lt then b.gram else a.gram   -- max
  crit := if compare a.crit b.crit = .lt then b.crit else a.crit   -- max
  chir := if compare a.chir b.chir = .lt then b.chir else a.chir   -- max
  stoi := if compare a.stoi b.stoi = .lt then b.stoi else a.stoi   -- max
  prot := if compare a.prot b.prot = .lt then b.prot else a.prot   -- max
}

-- P-bottleneck: O_inf ⊗ O_2 → P_pm_sym ⊗ P_sym = P_sym (Frobenius destroyed).
theorem tensor_P_bottleneck (a b : Imscription) :
    (tensorProduct a b).pol =
      if compare a.pol b.pol = .lt then a.pol else b.pol := rfl

-- ============================================================
-- OUROBORICITY OF AN IMSCRIPTION
-- ============================================================

def imscriptionTier (s : Imscription) : OuroboricityTier :=
  ouroboricityTier s.crit s.pol s.prot s.dim

-- ============================================================
-- KEY ENCODINGS
-- ============================================================

-- ── P-70: Scalar K_slow template (Higgs / axion / inflaton) ──
-- All three are spin-0 fields with double-well potential, slow-roll /
-- SSB relaxation (K_slow), symmetric potential (P_pm_sym at Phi_c).
-- They differ in energy scale only — not in primitive structure.
def scalarField_Kslow : Imscription := {
  dim  := D_triangle   -- local simplicial field (no holographic substrate)
  top  := T_bowtie     -- double-well / figure-8 potential landscape
  rel  := R_dagger     -- field ↔ vacuum bidirectional (SSB is reciprocal)
  pol  := P_pm_sym     -- exact Z_2 symmetry at Phi_c (μ ∘ δ = id)
  fid  := F_hbar       -- quantum coherent
  kin  := K_slow       -- slow-roll / thermally activated SSB (THE defining feature)
  gran := G_beth       -- mesoscale local description
  gram := Gamma_and    -- all SSB conditions required simultaneously
  crit := Phi_c        -- SSB is a phase transition
  chir := H1           -- soft temporal asymmetry (vacuum selection)
  stoi := n_n          -- field-to-excitation: matched coupling
  prot := Omega_0      -- no topological protection of the vacuum
}

def higgs : Imscription := scalarField_Kslow
def axion : Imscription := scalarField_Kslow
def inflaton : Imscription := scalarField_Kslow

/-- P-70a: Higgs and axion are structurally identical. -/
theorem P70a_higgs_axion_identity : higgs = axion := rfl

/-- P-70b: Axion and inflaton are structurally identical. -/
theorem P70b_axion_inflaton_identity : axion = inflaton := rfl

/-- P-70 (full): Three-scale K_slow symmetry. -/
theorem P70_three_scale_Kslow :
    higgs = axion ∧ axion = inflaton ∧ higgs = inflaton :=
  ⟨rfl, rfl, rfl⟩

/-- All three scalar K_slow fields are O_inf. -/
theorem scalar_Kslow_is_O_inf : imscriptionTier scalarField_Kslow = .O_inf := by decide

-- ── Standard Model ──────────────────────────────────────────
def standard_model : Imscription := {
  dim  := D_infty      -- 4D spacetime (unbounded temporal generation)
  top  := T_network    -- gauge group connections: general graph
  rel  := R_cat        -- compositional: gauge group × matter sector
  pol  := P_pm         -- Z_2 discrete symmetry (CP)
  fid  := F_eth        -- threshold: classical field theory with quantum corrections
  kin  := K_mod        -- perturbative (no confinement at this level)
  gran := G_aleph      -- all-scale: renormalization group runs to all scales
  gram := Gamma_and    -- gauge + matter + Higgs all simultaneously required
  crit := Phi_c        -- electroweak phase transition is a critical phenomenon
  chir := H2           -- persistent chirality (CKM matrix, neutrino mixing)
  stoi := n_m          -- many particles, unmatched coupling strengths
  prot := Omega_Z      -- instanton winding numbers (integer)
}

-- ── Quantum Gravity ─────────────────────────────────────────
-- D_odot and T_odot are co-required (Axiom C).
def quantum_gravity : Imscription := {
  dim  := D_odot       -- holographic: boundary encodes bulk
  top  := T_odot       -- holographic topology (co-required with D_odot)
  rel  := R_dagger     -- bulk ↔ boundary reciprocal
  pol  := P_pm_sym     -- diffeomorphism invariance at criticality: Special Frobenius
  fid  := F_hbar       -- quantum
  kin  := K_trap       -- Planck-scale dynamics are frozen at low energy
  gran := G_aleph      -- Planck-scale: all-to-all correlations
  gram := Gamma_broad  -- graviton couples universally (broadcast)
  crit := Phi_c        -- quantum criticality at Planck scale
  chir := H_inf        -- topological chirality (CPT asymmetry at Planck scale)
  stoi := n_m          -- many gravitational sources, unmatched
  prot := Omega_NA     -- non-Abelian topological protection
}

/-- Quantum gravity is O_inf (holographic Frobenius). -/
theorem qg_is_O_inf : imscriptionTier quantum_gravity = .O_inf := by decide

-- ── General Relativity ──────────────────────────────────────
def general_relativity : Imscription := {
  dim  := D_infty      -- 4D spacetime (not holographic — classical GR is local)
  top  := T_network    -- causal structure: general graph of events
  rel  := R_dagger     -- metric ↔ matter bidirectional (Einstein equations)
  pol  := P_sym        -- full diffeomorphism invariance
  fid  := F_hbar       -- classical limit of a quantum theory
  kin  := K_slow       -- geodesic motion is slow compared to Planck scale
  gran := G_gimel      -- collective: macroscopic description
  gram := Gamma_and    -- all matter + metric conditions simultaneously
  crit := Phi_sub      -- no quantum criticality in classical GR
  chir := H1           -- soft temporal asymmetry (arrow of time via initial conditions)
  stoi := n_n          -- matched: one metric for all matter
  prot := Omega_0      -- no topological protection
}

-- ── Yang-Mills (classical, pre-quantization) ────────────────
def yang_mills_classical : Imscription := {
  dim  := D_infty      -- 4D Minkowski spacetime
  top  := T_network    -- gauge group connections
  rel  := R_cat        -- compositional: gauge covariant derivative
  pol  := P_pm         -- Z_2 discrete parity
  fid  := F_eth        -- classical field theory
  kin  := K_mod        -- perturbative regime
  gran := G_beth       -- local: Lagrangian density at each point
  gram := Gamma_and    -- gauge invariance requires all conditions
  crit := Phi_sub      -- no mass gap yet
  chir := H1           -- weak temporal asymmetry
  stoi := n_n          -- gauge field ↔ matter: matched
  prot := Omega_Z      -- instanton winding numbers
}

-- ── Yang-Mills (quantum target) ─────────────────────────────
-- The target tuple if the path integral measure existed.
-- Gap from classical: F(eth→hbar), K(mod→trap), G(beth→aleph), Φ(sub→c) = 4 mismatches.
def yang_mills_quantum_target : Imscription := {
  dim  := D_infty
  top  := T_network
  rel  := R_cat
  pol  := P_pm
  fid  := F_hbar       -- quantum coherence
  kin  := K_trap       -- confinement = kinetic trapping
  gran := G_aleph      -- fine-grained: requires path integral measure
  gram := Gamma_and
  crit := Phi_c        -- mass gap is a critical phenomenon
  chir := H1
  stoi := n_n
  prot := Omega_Z
}

/-- The YM threshold is exactly 4 primitive mismatches. -/
theorem ym_threshold_4_primitives :
    primitiveMismatches yang_mills_classical yang_mills_quantum_target = 4 := by decide

-- ── SM ↔ QG distance ────────────────────────────────────────
/-- Standard Model and Quantum Gravity differ on 9 primitives. -/
theorem sm_qg_distance :
    primitiveMismatches standard_model quantum_gravity = 9 := by decide

-- ── GR → Asymptotic Safety: 3 primitive changes ─────────────
def asymptotic_safety : Imscription := { general_relativity with
  kin  := K_mod    -- UV fixed point has moderate kinetics
  gran := G_aleph  -- Planck-scale fine-grained
  crit := Phi_c    -- UV fixed point IS a quantum critical point
}

theorem gr_as_morphism_cost :
    primitiveMismatches general_relativity asymptotic_safety = 3 := by decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- Frobenius cliff: O_inf requires P_pm_sym. No other Polarity gives O_inf
    regardless of Φ, Ω, D. (Lean-verified statement of §23 / §69.) -/
theorem o_inf_iff_P_pm_sym_at_phi_c (s : Imscription) :
    imscriptionTier s = .O_inf ↔
    (s.crit = .Phi_c ∨ s.crit = .Phi_c_complex) ∧ s.pol = .P_pm_sym := by
  constructor
  · intro h
    constructor
    · exact o_inf_requires_phi_c s.crit s.pol s.prot s.dim h
    · exact o_inf_requires_P_pm_sym s.crit s.pol s.prot s.dim h
  · intro ⟨hphi, hpol⟩
    cases hphi with
    | inl h => simp [imscriptionTier, ouroboricityTier, h, hpol]
    | inr h => simp [imscriptionTier, ouroboricityTier, h, hpol]

/-- Higgs is O_inf (P-70 structural claim). -/
theorem higgs_is_O_inf : imscriptionTier higgs = .O_inf := by decide

/-- Tensor of O_inf with any O_2 system (P_sym) gives P_sym — Frobenius destroyed. -/
theorem tensor_O_inf_O2_destroys_frobenius (s_inf s_two : Imscription)
    (h_inf : s_inf.pol = .P_pm_sym) (h_two : s_two.pol = .P_sym) :
    (tensorProduct s_inf s_two).pol = .P_sym := by
  rw [tensorProduct, h_inf, h_two]
  rw [show compare (.P_pm_sym : Polarity) .P_sym = .gt by decide]
  rfl



-- ============================================================
-- SHAVIAN NOTATION LAYER (v0.6.0)
-- Each constructor maps to its Shavian glyph for display/output.
-- ============================================================

/-- Shavian notation for Dimensionality -/
def Dimensionality.shavian : Dimensionality → String
  | .D_wedge     => "𐑛"
  | .D_triangle  => "𐑨"
  | .D_infty     => "𐑼"
  | .D_odot      => "𐑦"

/-- Shavian notation for Topology -/
def Topology.shavian : Topology → String
  | .T_network  => "𐑡"
  | .T_in       => "𐑰"
  | .T_bowtie   => "𐑥"
  | .T_box      => "𐑶"
  | .T_odot     => "𐑸"

/-- Shavian notation for Relational -/
def Relational.shavian : Relational → String
  | .R_super  => "𐑩"
  | .R_cat    => "𐑑"
  | .R_dagger => "𐑽"
  | .R_lr     => "𐑾"

/-- Shavian notation for Polarity -/
def Polarity.shavian : Polarity → String
  | .P_asym   => "𐑗"
  | .P_psi    => "𐑿"
  | .P_pm     => "𐑬"
  | .P_sym    => "𐑯"
  | .P_pm_sym => "𐑹"

/-- Shavian notation for Fidelity -/
def Fidelity.shavian : Fidelity → String
  | .F_ell  => "𐑱"
  | .F_eth  => "𐑞"
  | .F_hbar => "𐑐"

/-- Shavian notation for KineticChar -/
def KineticChar.shavian : KineticChar → String
  | .K_fast => "𐑘"
  | .K_mod  => "𐑤"
  | .K_slow => "𐑧"
  | .K_trap => "𐑪"
  | .K_MBL  => "𐑺"

/-- Shavian notation for Granularity -/
def Granularity.shavian : Granularity → String
  | .G_beth  => "𐑚"
  | .G_gimel => "𐑔"
  | .G_aleph => "𐑲"

/-- Shavian notation for Grammar -/
def Grammar.shavian : Grammar → String
  | .Gamma_and   => "𐑝"
  | .Gamma_or    => "𐑜"
  | .Gamma_seq   => "𐑠"
  | .Gamma_broad => "𐑵"

/-- Shavian notation for Criticality -/
def Criticality.shavian : Criticality → String
  | .Phi_sub       => "𐑢"
  | .Phi_c         => "⊙"
  | .Phi_c_complex => "𐑮"
  | .Phi_EP        => "𐑻"
  | .Phi_super     => "𐑣"

/-- Shavian notation for Chirality -/
def Chirality.shavian : Chirality → String
  | .H0    => "𐑓"
  | .H1    => "𐑒"
  | .H2    => "𐑖"
  | .H_inf => "𐑫"

/-- Shavian notation for Stoichiometry -/
def Stoichiometry.shavian : Stoichiometry → String
  | .one_one => "𐑙"
  | .n_n     => "𐑕"
  | .n_m     => "𐑳"

/-- Shavian notation for Protection -/
def Protection.shavian : Protection → String
  | .Omega_0  => "𐑷"
  | .Omega_Z2 => "𐑴"
  | .Omega_Z  => "𐑭"
  | .Omega_NA => "𐑟"

/-- Render an Imscription as a Shavian tuple -/
def Imscription.shavian (s : Imscription) : String :=
  "⟨" ++ s.dim.shavian ++ "·" ++ s.top.shavian ++ "·" ++ s.rel.shavian ++ "·" ++
  s.pol.shavian ++ "·" ++ s.fid.shavian ++ "·" ++ s.kin.shavian ++ "·" ++
  s.gran.shavian ++ "·" ++ s.gram.shavian ++ "·" ++ s.crit.shavian ++ "·" ++
  s.chir.shavian ++ "·" ++ s.stoi.shavian ++ "·" ++ s.prot.shavian ++ "⟩"

/-- The Stone's tuple in Shavian -/
def stone_shavian : String :=
  (⟨D_odot, T_odot, R_lr, P_pm_sym, F_hbar, K_slow, G_aleph, Gamma_seq,
    Phi_c, H_inf, n_m, Omega_Z⟩ : Imscription).shavian

#eval stone_shavian
end Imscribing.Primitives
-- ============================================================
-- SHAVIAN NOTATION LAYER (v0.6.0)
-- Each constructor maps to its Shavian glyph for display/output.
-- ============================================================

namespace ShavianNotation
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-- Shavian glyph for Dimensionality -/
def dimShavian (d : Dimensionality) : String :=
  match d with
  | .D_wedge     => "𐑛"
  | .D_triangle  => "𐑨"
  | .D_infty     => "𐑼"
  | .D_odot      => "𐑦"

/-- Shavian glyph for Topology -/
def topShavian (t : Topology) : String :=
  match t with
  | .T_network  => "𐑡"
  | .T_in       => "𐑰"
  | .T_bowtie   => "𐑥"
  | .T_box      => "𐑶"
  | .T_odot     => "𐑸"

/-- Shavian glyph for Relational -/
def relShavian (r : Relational) : String :=
  match r with
  | .R_super  => "𐑩"
  | .R_cat    => "𐑑"
  | .R_dagger => "𐑽"
  | .R_lr     => "𐑾"

/-- Shavian glyph for Polarity -/
def polShavian (p : Polarity) : String :=
  match p with
  | .P_asym   => "𐑗"
  | .P_psi    => "𐑿"
  | .P_pm     => "𐑬"
  | .P_sym    => "𐑯"
  | .P_pm_sym => "𐑹"

/-- Shavian glyph for Fidelity -/
def fidShavian (f : Fidelity) : String :=
  match f with
  | .F_ell  => "𐑱"
  | .F_eth  => "𐑞"
  | .F_hbar => "𐑐"

/-- Shavian glyph for KineticChar -/
def kinShavian (k : KineticChar) : String :=
  match k with
  | .K_fast => "𐑘"
  | .K_mod  => "𐑤"
  | .K_slow => "𐑧"
  | .K_trap => "𐑪"
  | .K_MBL  => "𐑺"

/-- Shavian glyph for Granularity -/
def granShavian (g : Granularity) : String :=
  match g with
  | .G_beth  => "𐑚"
  | .G_gimel => "𐑔"
  | .G_aleph => "𐑲"

/-- Shavian glyph for Grammar -/
def gramShavian (g : Grammar) : String :=
  match g with
  | .Gamma_and   => "𐑝"
  | .Gamma_or    => "𐑜"
  | .Gamma_seq   => "𐑠"
  | .Gamma_broad => "𐑵"

/-- Shavian glyph for Criticality -/
def critShavian (c : Criticality) : String :=
  match c with
  | .Phi_sub       => "𐑢"
  | .Phi_c         => "⊙"
  | .Phi_c_complex => "𐑮"
  | .Phi_EP        => "𐑻"
  | .Phi_super     => "𐑣"

/-- Shavian glyph for Chirality -/
def chirShavian (h : Chirality) : String :=
  match h with
  | .H0    => "𐑓"
  | .H1    => "𐑒"
  | .H2    => "𐑖"
  | .H_inf => "𐑫"

/-- Shavian glyph for Stoichiometry -/
def stoiShavian (s : Stoichiometry) : String :=
  match s with
  | .one_one => "𐑙"
  | .n_n     => "𐑕"
  | .n_m     => "𐑳"

/-- Shavian glyph for Protection -/
def protShavian (p : Protection) : String :=
  match p with
  | .Omega_0  => "𐑷"
  | .Omega_Z2 => "𐑴"
  | .Omega_Z  => "𐑭"
  | .Omega_NA => "𐑟"

/-- Render a full Imscription tuple in Shavian notation. -/
def imscriptionShavian (s : Imscription) : String :=
  "⟨" ++ dimShavian s.dim ++ "·" ++ topShavian s.top ++ "·" ++ relShavian s.rel ++ "·" ++
  polShavian s.pol ++ "·" ++ fidShavian s.fid ++ "·" ++ kinShavian s.kin ++ "·" ++
  granShavian s.gran ++ "·" ++ gramShavian s.gram ++ "·" ++ critShavian s.crit ++ "·" ++
  chirShavian s.chir ++ "·" ++ stoiShavian s.stoi ++ "·" ++ protShavian s.prot ++ "⟩"

/-- The Stone's tuple in Shavian: ⟨𐑦·𐑸·𐑾·𐑹·𐑐·𐑧·𐑲·𐑠·⊙·𐑫·𐑳·𐑭⟩ -/
def stoneShavian : String :=
  imscriptionShavian ⟨D_odot, T_odot, R_lr, P_pm_sym, F_hbar, K_slow, G_aleph, Gamma_seq,
    Phi_c, H_inf, n_m, Omega_Z⟩

#eval! stoneShavian

end ShavianNotation
