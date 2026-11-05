/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfLinkFirstMoment
public import WaveTurbulence.Foundations.RegAsymp.TensorAmplitudeBudget

/-! # The actual smooth localized amplitude used in NT -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh MeasureTheory
open scoped ENNReal FourierTransform

/-- Retain the actual half-cells as the NT amplitude and insert only the
linear modulations supplied by the leaf-frequency pullback. -/
def halfCellAmplitude {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) (x y : Fin n → Mom d) : ℂ :=
  (∏ j, Real.fourierChar (inner ℝ (β j) (x j)) • halfLinkCell (z (j,0)) (x j)) *
    (∏ j, Real.fourierChar (inner ℝ (γ j) (y j)) • halfLinkCell (z (j,1)) (y j))

/-- The actual half-cell profiles have measurable Euclidean Fourier transforms. -/
theorem measurable_fourier_halfLinkCell {d : ℕ} (c : Fin d → ℤ) :
    Measurable (𝓕 (halfLinkCell c)) := by
  have hi : Integrable (halfLinkCell c) := (contDiff_halfLinkCell c).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_halfLinkCell c)
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi).measurable

/-- The true NT amplitude budget is linear in the sum of modulation
lengths and geometric in the number of independent actual half-cells. -/
theorem halfCellAmplitude_fourier_budget {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) :
    (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖ApproxNT.fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*ApproxNT.freqNorm τ.1 τ.2)) ≤
      ENNReal.ofReal (1+2*Real.pi) *
        (ENNReal.ofReal (1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖))) *
          ENNReal.ofReal (halfLinkFirstMomentConstant d) ^ (2*n)) := by
  have hh := fourierW_modulated_tensor_budget (fun j => halfLinkCell (z (j,0)))
    (fun j => halfLinkCell (z (j,1))) (fun j => measurable_fourier_halfLinkCell (z (j,0)))
    (fun j => measurable_fourier_halfLinkCell (z (j,1))) β γ
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  calc
    _ ≤ (∏ _j : Fin n, ENNReal.ofReal (halfLinkFirstMomentConstant d)) *
        (∏ _j : Fin n, ENNReal.ofReal (halfLinkFirstMomentConstant d)) :=
      mul_le_mul' (Finset.prod_le_prod (fun j _ => halfLinkCell_euclidean_firstMoment_lintegral_le (z (j,0))))
        (Finset.prod_le_prod (fun j _ => halfLinkCell_euclidean_firstMoment_lintegral_le (z (j,1))))
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rw [← pow_add]; congr 1; omega

end WaveTurbulence.RegAsymp
