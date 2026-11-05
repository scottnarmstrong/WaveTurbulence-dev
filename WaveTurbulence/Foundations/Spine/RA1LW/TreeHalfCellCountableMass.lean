/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFourierMixture
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSingularCellMass

/-! # Actual absolute Fourier mass of a countable family of retained half cells -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

variable {I U : Type*} [MeasurableSpace U] {d n : ℕ}

/-- Each counted source half cell has its original finite ordinary-cell cover. -/
abbrev TreeHalfCellOrdinaryIndex (z : I → (Fin n × Fin 2) → Fin d → ℤ) :=
  Σ c : I, halfCellOrdinaryCells (z c)

/-- The actual joint coefficient; selecting an ordinary support cell does not change it. -/
def treeHalfCellCountableCoefficient
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (a : I → U → ℂ) (i : TreeHalfCellOrdinaryIndex z)
    (p : U × ((Fin n → Mom d) × (Fin n → Mom d))) : ℂ :=
  a i.1 p.1 * fourierW (halfCellAmplitude (z i.1) (β p.1) (γ p.1)) p.2.1 p.2.2

/-- Strong measurability retains the original counted half-cell positions. -/
theorem stronglyMeasurable_treeHalfCellCountableCoefficient
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c)) (i : TreeHalfCellOrdinaryIndex z) :
    StronglyMeasurable (treeHalfCellCountableCoefficient z β γ a i) :=
  stronglyMeasurable_halfCellFourierMixture (z i.1) β γ hβ hγ (a i.1) (ha i.1)

/-- Actual first modulation moments give joint L1, before singular integration. -/
theorem integrable_treeHalfCellCountableCoefficient
    (μ : Measure U) [SFinite μ] (hn : 0 < n)
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (i : TreeHalfCellOrdinaryIndex z) :
    Integrable (treeHalfCellCountableCoefficient z β γ a i) (μ.prod volume) :=
  (halfCellFourierMixture_integrable_mass μ hn (z i.1) β γ hβ hγ (a i.1) (ha i.1) (hi i.1)).1

/-- The actual first-moment masses give summability over every original source cell
and its actual finite ordinary cover. No singular-convergence premise is assumed. -/
theorem summable_integral_norm_treeHalfCellCountableCoefficient
    (μ : Measure U) [SFinite μ] (hn : 0 < n)
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ)) :
    Summable (fun i : TreeHalfCellOrdinaryIndex z =>
      ∫ p, ‖treeHalfCellCountableCoefficient z β γ a i p‖ ∂μ.prod volume) := by
  let f := fun c => ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
    ‖a c p.1 * fourierW (halfCellAmplitude (z c) (β p.1) (γ p.1)) p.2.1 p.2.2‖ ∂μ.prod volume
  have hf (c : I) : 0 ≤ f c := integral_nonneg (fun _ => norm_nonneg _)
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le hf _ (hs.mul_left ((1+2*Real.pi)*halfLinkFirstMomentConstant d^(2*n)))
    intro c
    exact (halfCellFourierMixture_integrable_mass μ hn (z c) β γ hβ hγ (a c) (ha c) (hi c)).2
  exact summable_sigma_finite_fiber_of_card_le hf hsum
    (C := ((2*max 1 (Real.sqrt d)+5)^(2*d))^n)
    (fun c => by simpa only [Fintype.card_coe] using card_halfCellOrdinaryCells_le (z c))

end WaveTurbulence.RA1Leafwise
