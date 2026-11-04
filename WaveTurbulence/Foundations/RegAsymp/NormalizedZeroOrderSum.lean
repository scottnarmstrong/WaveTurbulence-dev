/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ZeroOrderApproximation
public import WaveTurbulence.Foundations.ApproxNT.PsiOne

/-! # Size of the actual empty-link NT sum -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT
open scoped ContDiff

/-- The normalized derivative premise also bounds the empty-variable
symbol; it does not require a positive-order NT theorem. -/
theorem norm_approxSum_zero_order_le {d : ℕ} (L μ : ℝ)
    (W : (Fin 0 → Mom d) → (Fin 0 → Mom d) → ℂ)
    (J : Finset (Fin 0)) (Ψ : EuclideanSpace ℝ {j : Fin 0 // j ∉ J} → ℂ)
    (hΨ : ContDiff ℝ ∞ Ψ) (hD : WordDerivL1 Ψ (fun k => ((4*k).factorial:ℝ)))
    {H : ℝ} (hW : ‖W 0 0‖ ≤ H) : ‖approxSum L μ W (resProfile J Ψ)‖ ≤ H := by
  have hnorm : ‖Ψ 0‖ ≤ 1 := by
    have hh := integral_norm_wordDeriv_le hΨ hD (fun k => by positivity) (k := 0) Fin.elim0
    simpa [wordDeriv,iteratedFDeriv_zero_apply,volume_euclideanSpace_eq_dirac] using hh
  rw [approxSum_zero_order,resProfile_zero_order,norm_mul]
  calc
    _ ≤ ‖W 0 0‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ H := by simpa only [mul_one] using hW

end WaveTurbulence.RegAsymp
