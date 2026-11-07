/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceWeightExpansion
public import WaveTurbulence.Foundations.SumintPar.TensorCharacter

/-!
# The exact localized source Fourier coefficient

The primary and alternative weights remain separate until their Fourier
expansion has been taken. The resulting coefficient is integrable and
continuous and retains the source multiplicity decay.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped FourierTransform

namespace WaveTurbulence.SumintPar

/-- The tensor Fourier coefficient for the two actual source weight families. -/
@[expose] noncomputable def sourceCoefficient {d : ℕ} (D : SumintDatum d)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) : ℂ :=
  ∏ i, 𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D r i)) (ξ i)

/-- The actual coefficient has finite absolute mass. -/
theorem integrable_sourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) : Integrable (sourceCoefficient D a b r) :=
  source_tensor_fourier_integrable hd D hL hD r (Sum.elim a b)

/-- The coefficient's mass keeps the full source weight-multiplicity gain. -/
theorem integral_norm_sourceCoefficient_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) :
    (∫ ξ, ‖sourceCoefficient D a b r ξ‖) ≤
      cellFourierFactor d^(2*D.S.M)*L^(-(gammaWeight d γ-Real.sqrt η)*D.M₁) :=
  source_tensor_fourier_mass_le hd D hL hD r (Sum.elim a b)

/-- The actual tensor coefficient is continuous in all frequency coordinates. -/
theorem continuous_sourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) : Continuous (sourceCoefficient D a b r) := by
  unfold sourceCoefficient
  apply continuous_finsetProd
  intro i _
  have hf := contDiff_of_SNorm_le hD.wN_ne_zero (sourceWeight_bound D hD r i)
  have hi : Integrable (localizedWeight (Sum.elim a b i) (sourceWeight D r i)) :=
    (localizedWeight_contDiff _ hf).continuous.integrable_of_hasCompactSupport
      (localizedWeight_hasCompactSupport _ _)
  have hc : Continuous (𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D r i))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  exact hc.comp (continuous_apply i)

/-- The modulation times coefficient is genuinely integrable at every lattice input. -/
theorem integrable_source_modulatedCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    Integrable (fun ξ => tensorCharacter (Sum.elim (D.kVec L x E) (D.ℓVec L x E)) ξ *
      sourceCoefficient D a b (E 0 - E 1) ξ) :=
  integrable_tensorCharacter_mul _ (integrable_sourceCoefficient hd D hL hD a b _)

/-- Exact localized weight expansion in separated character/coefficient form. -/
theorem source_coefficient_expansion {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    (∫ ξ, tensorCharacter (Sum.elim (D.kVec L x E) (D.ℓVec L x E)) ξ *
      sourceCoefficient D a b (E 0 - E 1) ξ) =
      ∏ v, localizedWeight (a v) (D.wK v (E 0 - E 1)) (D.kVec L x E v) *
        localizedWeight (b v) (D.wL v) (D.ℓVec L x E v) := by
  calc
    _ = ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
        ∏ i, (Real.fourierChar (inner ℝ (ξ i) (Sum.elim (D.kVec L x E) (D.ℓVec L x E) i)) : ℂ) *
          𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D (E 0 - E 1) i)) (ξ i) := by
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      unfold tensorCharacter sourceCoefficient
      exact (Finset.prod_mul_distrib).symm
    _ = _ := source_localized_weights_expansion hd D hL hD a b x E

end WaveTurbulence.SumintPar
