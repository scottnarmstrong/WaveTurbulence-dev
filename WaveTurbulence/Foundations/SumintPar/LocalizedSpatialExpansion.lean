/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoefficient
public import WaveTurbulence.Foundations.SumintPar.AffineCharacter

/-!
# Exact localized spatial expansion of the source oscillatory sum

The cutoff centres are chosen once for each pair of localization labels,
independently of output momenta and all times. Compact support makes the
spatial sum finite before Fourier Fubini is used. The resulting expression
has exactly the independent input modulation and the external unit phase.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset

namespace WaveTurbulence.SumintPar

/-- The literal primary/alternative localized weight product. -/
@[expose] noncomputable def localizedSourceWeight {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (x : D.S.VIdx → Fin d → ℤ) : ℂ :=
  ∏ v, localizedWeight (a v) (D.wK v (E 0 - E 1)) (D.kVec L x E v) *
    localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)

end WaveTurbulence.SumintPar
