/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionFourier

/-!
# Genuine regularity of the Fourier-recombined localized extension

The exact finite spatial inversion supplies pointwise measurability and
time integrability before localization labels are summed.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The actual Fourier-recombined localized extension is measurable everywhere. -/
theorem measurable_localizedSourceExtension {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d) :
    Measurable (localizedSourceExtension D hI N h L γ δ η a b p E) := by
  have he := funext (localizedSourceExtension_eq_sum (δ := δ) hd D hI N h hL hη hD a b p E)
  rw [he]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro x _
  exact measurable_const.mul (measurable_phaseCellExtension D hI N h L γ δ η x (E 0-E 1))

/-- The actual Fourier-recombined localized extension satisfies the ambient time guard. -/
theorem integrable_localizedSourceExtension {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d) :
    Integrable (localizedSourceExtension D hI N h L γ δ η a b p E) := by
  have he := funext (localizedSourceExtension_eq_sum (δ := δ) hd D hI N h hL hη hD a b p E)
  rw [he]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro x _
  exact (integrable_phaseCellExtension D hI N h L γ δ η hη x (E 0-E 1)).const_mul _

end WaveTurbulence.Sumint
