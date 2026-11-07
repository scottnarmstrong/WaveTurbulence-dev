/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.AffineCharacter
public import WaveTurbulence.Foundations.SumintPar.NormalizedSourceCoefficient

/-!
# Regularity of the actual transposed spatial modulation maps

The affine matrices are fixed real coefficients. Their input and
external Fourier characters are continuous in all spatial frequencies.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.SumintPar

/-- The actual transposed input modulation is continuous in both frequency families. -/
theorem continuous_sourceInputModulation {d : ℕ} (D : SumintDatum d) :
    Continuous (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) := by
  unfold inputModulation
  fun_prop

/-- The actual external affine character is continuous in the spatial frequencies. -/
theorem continuous_sourceExternalCharacter {d : ℕ} (D : SumintDatum d) (E : Fin 4 → Mom d) :
    Continuous (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ)) := by
  apply (continuous_subtype_val.comp Real.continuous_fourierChar).comp
  unfold externalModulation
  fun_prop

/-- The actual normalized coefficient is continuous in all spatial frequencies. -/
theorem continuous_normalizedSourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) :
    Continuous (normalizedSourceCoefficient D L γ η a b r) :=
  continuous_const.mul (continuous_sourceCoefficient hd D hD a b r)

end WaveTurbulence.SumintPar
