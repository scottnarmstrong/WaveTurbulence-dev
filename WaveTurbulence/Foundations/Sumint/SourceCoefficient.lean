/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceWeightExpansion
public import WaveTurbulence.Foundations.Sumint.TensorCharacter

/-!
# The exact localized source Fourier coefficient

The primary and alternative weights remain separate until their Fourier
expansion has been taken. The resulting coefficient is integrable and
continuous and retains the source multiplicity decay.
-/

public section

open MeasureTheory Finset
open scoped FourierTransform

namespace WaveTurbulence.Sumint

/-- The tensor Fourier coefficient for the two actual source weight families. -/
@[expose] noncomputable def sourceCoefficient {d : ℕ} (D : SumintDatum d)
    (a b : D.S.VIdx → Fin d → ℤ) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) : ℂ :=
  ∏ i, 𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D i)) (ξ i)

/-- The actual coefficient has finite absolute mass. -/
theorem integrable_sourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) : Integrable (sourceCoefficient D a b) :=
  source_tensor_fourier_integrable hd D hL hD (Sum.elim a b)

/-- The actual tensor coefficient is continuous in all frequency coordinates. -/
theorem continuous_sourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) : Continuous (sourceCoefficient D a b) := by
  unfold sourceCoefficient
  apply continuous_finsetProd
  intro i _
  have hf := contDiff_of_SNorm_le (by omega : 30*d ≠ 0) (sourceWeight_bound D hD i)
  have hi : Integrable (localizedWeight (Sum.elim a b i) (sourceWeight D i)) :=
    (localizedWeight_contDiff _ hf).continuous.integrable_of_hasCompactSupport
      (localizedWeight_hasCompactSupport _ _)
  have hc : Continuous (𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D i))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  exact hc.comp (continuous_apply i)

/-- Exact localized weight expansion in separated character/coefficient form. -/
theorem source_coefficient_expansion {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    (∫ ξ, tensorCharacter (Sum.elim (D.kVec L x E) (D.ℓVec L x E)) ξ *
      sourceCoefficient D a b ξ) =
      ∏ v, localizedWeight (a v) (D.wK v) (D.kVec L x E v) *
        localizedWeight (b v) (D.wL v) (D.ℓVec L x E v) := by
  calc
    _ = ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
        ∏ i, (Real.fourierChar (inner ℝ (ξ i) (Sum.elim (D.kVec L x E) (D.ℓVec L x E) i)) : ℂ) *
          𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D i)) (ξ i) := by
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      unfold tensorCharacter sourceCoefficient
      exact (Finset.prod_mul_distrib).symm
    _ = _ := source_localized_weights_expansion hd D hL hD a b x E

end WaveTurbulence.Sumint
