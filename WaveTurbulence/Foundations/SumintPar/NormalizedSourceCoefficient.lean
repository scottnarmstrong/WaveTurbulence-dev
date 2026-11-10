/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTotalCoefficientMass
public import WaveTurbulence.Foundations.SumintPar.WeightedCutoffInput

/-!
# Source coefficients normalized by the weight decay already inside the kernel

The actual kernel coefficient contains sourceWeightDecay. Divide the
spatial Fourier coefficient by this strictly positive real scalar, so
recombination restores the original source expression exactly and the
weight gain is counted once. The normalized total coefficient mass has
only a constant to the literal input count.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The actual source weight decay is strictly positive at positive lattice scale. -/
theorem sourceWeightDecay_pos {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ) :
    0 < sourceWeightDecay D L γ η := Real.rpow_pos_of_pos hL _

/-- Normalize the spatial Fourier coefficient by the strictly positive decay already included in the time kernel. -/
@[expose] noncomputable def normalizedSourceCoefficient {d : ℕ} (D : SumintDatum d) (L γ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) : ℂ :=
  (((sourceWeightDecay D L γ η)⁻¹:ℝ):ℂ)*sourceCoefficient D a b r ξ

/-- The normalized coefficient is genuinely integrable. -/
theorem integrable_normalizedSourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η N)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) : Integrable (normalizedSourceCoefficient D L γ η a b r) :=
  (integrable_sourceCoefficient hd D hL hD a b r).const_mul _

end WaveTurbulence.SumintPar
