/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Density
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawModulation
public import WaveTurbulence.Foundations.Incoh.SourceTemporalPhase

/-! # D5b-1 FILT-SRC: the filtered source temporal phase (D5B-MAP K2)

The per-array filter factor `arrayFiltWeight L φ p = ∏_i φ_i (⟨x_i, y_i⟩)` (`x_i, y_i` the lattice points of
`p (i, 0), p (i, 1)`, D5a `linkBilinear`), and the twins of
- main's `Incoh.sourceTemporalPhase` (`Incoh/SourceTemporalPhase.lean`): `sourceTemporalPhaseFilt`;
- INC-TOP's `Reg.sourceTemporalPhaseSpatial` (`IncTop/Reg/SourceTemporalPhase.lean`): `sourceTemporalPhaseSpatialFilt`;
- INC-TOP's `Reg/RawModulation` character identity and joint continuity.

Each twin carries `φ_i (⟨x_i, y_i⟩)` inside the factor of link `i`, and equals the original times
`arrayFiltWeight L φ p` (`…_eq`). The phase bound `≤ 1` becomes `≤ Bφ ^ n` when `‖φ_i‖ ≤ Bφ` (D5B-MAP K2: `B^{4n}` at
worst through D5a `exists_linkFiltWeight_bound`). Copied by source (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop

variable {d n : ℕ}

/-- **The filter factor of a link array**: link `i` carries `φ i` at its bilinear frequency `⟨x_i, y_i⟩`. -/
def arrayFiltWeight (L : ℝ) (φ : Fin n → ℝ → ℂ) (p : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ∏ i, φ i (linkBilinear L (p (i, 0), p (i, 1)))

theorem norm_arrayFiltWeight_le (L : ℝ) (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) : ‖arrayFiltWeight L φ p‖ ≤ Bφ ^ n := by
  rw [arrayFiltWeight, norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, Bφ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hφ i _)
    _ = Bφ ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Twin of main's `Incoh.SourceTemporalPhase` -/

/-- **The filtered Wick-corrected temporal factor** at fixed free lattice momenta (twin of `sourceTemporalPhase`). -/
def sourceTemporalPhaseFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∏ i, (linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) * φ i (linkBilinear L (p (i, 0), p (i, 1))) *
    WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1) * inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1))))

theorem sourceTemporalPhaseFilt_eq (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhaseFilt L γ δ Q φ p t = sourceTemporalPhase L γ δ Q p t * arrayFiltWeight L φ p := by
  rw [sourceTemporalPhaseFilt, sourceTemporalPhase, arrayFiltWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Filtered source phases are continuous in all vertex clocks. -/
theorem continuous_sourceTemporalPhaseFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) : Continuous (sourceTemporalPhaseFilt L γ δ Q φ p) := by
  have h : sourceTemporalPhaseFilt L γ δ Q φ p = fun t => sourceTemporalPhase L γ δ Q p t * arrayFiltWeight L φ p := by
    funext t
    exact sourceTemporalPhaseFilt_eq L γ δ Q φ p t
  rw [h]
  exact (continuous_sourceTemporalPhase L γ δ Q p).mul continuous_const

/-- The filtered phase is bounded by the filter bound: `‖·‖ ≤ Bφ ^ n`. -/
theorem norm_sourceTemporalPhase_leFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    ‖sourceTemporalPhaseFilt L γ δ Q φ p t‖ ≤ Bφ ^ n := by
  rw [sourceTemporalPhaseFilt_eq, norm_mul]
  calc
    _ ≤ 1 * Bφ ^ n := mul_le_mul (norm_sourceTemporalPhase_le_one L γ δ Q p t)
      (norm_arrayFiltWeight_le L φ hφ p) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Every filtered source phase is integrable on any source time subdomain of the layer box. -/
theorem integrableOn_sourceTemporalPhaseFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (sourceTemporalPhaseFilt L γ δ Q φ p) I :=
  ((continuous_sourceTemporalPhaseFilt L γ δ Q φ p).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set hI

/-! ### Twin of INC-TOP's `Reg/SourceTemporalPhase` -/

/-- **The filtered spatially modulated source phase** (twin of INC-TOP's `sourceTemporalPhaseSpatial`). -/
def sourceTemporalPhaseSpatialFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∏ i, (linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) * φ i (linkBilinear L (p (i, 0), p (i, 1))) *
    WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1) * inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1))) +
      inner ℝ (latticePoint L (p (i, 0))) (Q i).leftShift +
      inner ℝ (latticePoint L (p (i, 1))) (Q i).rightShift)

theorem sourceTemporalPhaseSpatialFilt_eq (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhaseSpatialFilt L γ δ Q φ p t =
      sourceTemporalPhaseSpatial L γ δ Q p t * arrayFiltWeight L φ p := by
  rw [sourceTemporalPhaseSpatialFilt, sourceTemporalPhaseSpatial, arrayFiltWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem continuous_sourceTemporalPhaseSpatialFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    Continuous (sourceTemporalPhaseSpatialFilt L γ δ Q φ p) := by
  have h : sourceTemporalPhaseSpatialFilt L γ δ Q φ p =
      fun t => sourceTemporalPhaseSpatial L γ δ Q p t * arrayFiltWeight L φ p := by
    funext t
    exact sourceTemporalPhaseSpatialFilt_eq L γ δ Q φ p t
  rw [h]
  exact (continuous_sourceTemporalPhaseSpatial L γ δ Q p).mul continuous_const

theorem norm_sourceTemporalPhase_leSpatialFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    ‖sourceTemporalPhaseSpatialFilt L γ δ Q φ p t‖ ≤ Bφ ^ n := by
  rw [sourceTemporalPhaseSpatialFilt_eq, norm_mul]
  calc
    _ ≤ 1 * Bφ ^ n := mul_le_mul (norm_sourceTemporalPhase_le_oneSpatial L γ δ Q p t)
      (norm_arrayFiltWeight_le L φ hφ p) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem integrableOn_sourceTemporalPhaseSpatialFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (p : (Fin n × Fin 2) → Fin d → ℤ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (sourceTemporalPhaseSpatialFilt L γ δ Q φ p) I :=
  ((continuous_sourceTemporalPhaseSpatialFilt L γ δ Q φ p).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set hI

/-! ### Twins of INC-TOP's `Reg/RawModulation` (character identity, joint continuity) -/

/-- The filtered internal character identity, before lattice or clock integration. -/
theorem sourceTemporalPhaseSpatialFilt_eq_character (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (ν : PairedMomentum d n) (p : (Fin n × Fin 2) → Fin d → ℤ)
    (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhaseSpatialFilt L γ δ (spatialFrequencyLinks Q ν) φ p t =
      sourceTemporalPhaseFilt L γ δ Q φ p t * (Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) := by
  rw [sourceTemporalPhaseSpatialFilt_eq, sourceTemporalPhaseFilt_eq, sourceTemporalPhaseSpatial_eq_character]
  ring

/-- Joint continuity of the filtered phase in all spatial frequencies and all internal clocks. -/
theorem continuous_sourceTemporalPhaseSpatialFilt_frequency (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    Continuous (fun z : PairedMomentum d n × (Fin n → Fin 2 → ℝ) =>
      sourceTemporalPhaseSpatialFilt L γ δ (spatialFrequencyLinks Q z.1) φ p z.2) := by
  simp_rw [sourceTemporalPhaseSpatialFilt_eq]
  exact (continuous_sourceTemporalPhaseSpatial_frequency L γ δ Q p).mul continuous_const

end WaveTurbulence.Flower.FiltSrc
