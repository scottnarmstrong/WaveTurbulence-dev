/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValue

/-!
# Bounds and cutoff independence for the inverse-energy principal value

These estimates depend on the normal derivative of the kernel. They establish
well-definedness and bounds for the principal value; they do not replace the
stronger frequency-uniform estimate in DH21 Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal

namespace WaveTurbulence

variable {d : ℕ}
variable {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
variable {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ}
variable (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
variable (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
variable (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)

include hF hgrad hDc hD hR hs

/-- A cutoff-free absolute bound for the limit of a slice. -/
theorem abs_energyInvSliceLimit_le {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    |energyInvSliceLimit F ℓ| ≤ (R * hypConst d M) * (‖ℓ‖⁻¹ * B ℓ) := by
  rw [energyInvSliceLimit, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hq := integral_abs_pvQuotient_le (hF.continuous_sliceInt hℓ)
    (hasDerivAt_sliceInt hF hgrad hDc hD hℓ 0).differentiableAt
    (hasCompactSupport_sliceInt hs hℓ) (lipschitzWith_sliceInt hF hgrad hDc hD hℓ)
    hR (fun t ht => sliceInt_eq_zero_of_radius hs hℓ ht)
  have hi : |∫ t, pvQuotient (sliceInt F ℓ) t| ≤
      ∫ t, |pvQuotient (sliceInt F ℓ) t| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (pvQuotient (sliceInt F ℓ))
  refine (mul_le_mul_of_nonneg_left (hi.trans hq) (by positivity)).trans_eq ?_
  change (2 * ‖ℓ‖)⁻¹ * (2 * R * (B ℓ * hypConst d M)) = _
  rw [mul_inv]
  ring

/-- The symmetric-quotient representation has an integrable outer integrand. -/
theorem integrable_energyInvSliceLimit (hd : 0 < d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    Integrable (energyInvSliceLimit F) := by
  have hm : AEStronglyMeasurable (energyInvSliceLimit F) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun μ => (hF.stronglyMeasurable_energyInvInner hχ μ).aestronglyMeasurable)
      ((DeltaKernel.ae_ne_zero hd).mono fun ℓ hℓ =>
        tendsto_energyInvInner hF hgrad hDc hD hs hχ hℓ)
  refine (hgrad.integrable.const_mul (R * hypConst d M)).mono' hm ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs]
  exact abs_energyInvSliceLimit_le hF hgrad hDc hD hR hs hℓ

/-- Absolute bound for the principal value; the constant uses only the support
radius and the integrable gradient-decay profile. -/
theorem abs_energyPrincipalValue_le (hd : 0 < d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    |energyPrincipalValue F D hd hF hgrad hDc hD hR hs χ hχ| ≤
      (R * hypConst d M) * ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * B ℓ := by
  rw [energyPrincipalValue_eq_integral, ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hgrad.integrable.const_mul _) ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs]
  exact abs_energyInvSliceLimit_le hF hgrad hDc hD hR hs hℓ

/-- Changing the even cutoff leaves the principal value unchanged. -/
theorem energyPrincipalValue_cutoff_independent (hd : 0 < d) {χ ψ : ℝ → ℝ}
    (hχ : IsPVCutoff χ) (hψ : IsPVCutoff ψ) :
    energyPrincipalValue F D hd hF hgrad hDc hD hR hs χ hχ =
      energyPrincipalValue F D hd hF hgrad hDc hD hR hs ψ hψ := by
  rw [energyPrincipalValue_eq_integral, energyPrincipalValue_eq_integral]

end WaveTurbulence
