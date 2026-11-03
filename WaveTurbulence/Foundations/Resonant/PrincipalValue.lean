/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueSlices
public import WaveTurbulence.Foundations.Resonant.PrincipalValueBounds
public import WaveTurbulence.Foundations.Resonant.SliceRegularity

/-!
# Existence of the principal value of the inverse energy resonance

For a continuously differentiable kernel with an integrable polynomial decay
profile for its gradient and a uniform support radius in the second momentum,
the cutoff limit for `1/(-2⟨ℓ,x⟩)` exists. Both finite iterated integrals are
honest Bochner integrals. This provides existence in the parametrization of
the frozen collision operator; it does not assert frequency-uniform estimates.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace NNReal

namespace WaveTurbulence

variable {d : ℕ}

/-- Finite cutoff integral of the inverse energy resonance. -/
@[expose] noncomputable def energyInvIntegral (χ : ℝ → ℝ) (μ : ℝ)
    (F : Mom d → Mom d → ℝ) : ℝ := ∫ ℓ, energyInvInner χ μ F ℓ

/-- Absolutely convergent symmetric-quotient representation of the slice limit. -/
@[expose] noncomputable def energyInvSliceLimit (F : Mom d → Mom d → ℝ) (ℓ : Mom d) : ℝ :=
  -(2 * ‖ℓ‖)⁻¹ * ∫ t, pvQuotient (sliceInt F ℓ) t

theorem DeltaKernel.stronglyMeasurable_energyInvInner
    {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {a : Mom d → Mom d} {N : ℝ}
    (hF : DeltaKernel F A a N) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) :
    StronglyMeasurable (energyInvInner χ μ F) := by
  apply StronglyMeasurable.integral_prod_right
  apply Continuous.stronglyMeasurable
  exact hF.cont.mul ((hχ.continuous_div μ).comp
    ((continuous_const.mul (continuous_fst.inner continuous_snd)).neg))

/-- Convergence of each nondegenerate slice. -/
theorem tendsto_energyInvInner
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Tendsto (fun μ => energyInvInner χ μ F ℓ) atTop (𝓝 (energyInvSliceLimit F ℓ)) := by
  have ht := hχ.tendsto_pvTruncation (hF.continuous_sliceInt hℓ)
    (hasDerivAt_sliceInt hF hgrad hDc hD hℓ 0).differentiableAt
    (hasCompactSupport_sliceInt hs hℓ)
  have ha : 0 < 2 * ‖ℓ‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hℓ)
  have hscale : Tendsto (fun μ : ℝ => μ * (2 * ‖ℓ‖)) atTop atTop :=
    Tendsto.atTop_mul_const ha tendsto_id
  exact ((ht.comp hscale).const_mul (-(2 * ‖ℓ‖)⁻¹)).congr
    (fun μ => (hF.energyInvInner_eq hχ μ hℓ).symm)

/-- A scale-uniform integrable bound for the outer integral. -/
theorem abs_energyInvInner_le
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R C : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hC : ∀ u, |χ u| ≤ C)
    (μ : ℝ) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    |energyInvInner χ μ F ℓ| ≤
      (R * (1 + C) * hypConst d M) * (‖ℓ‖⁻¹ * B ℓ) := by
  rw [hF.energyInvInner_eq hχ μ hℓ, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hb := abs_pvTruncation_le_radius hχ (hF.continuous_sliceInt hℓ)
    (hasDerivAt_sliceInt hF hgrad hDc hD hℓ 0).differentiableAt
    (hasCompactSupport_sliceInt hs hℓ) (lipschitzWith_sliceInt hF hgrad hDc hD hℓ)
    hR (fun t ht => sliceInt_eq_zero_of_radius hs hℓ ht) hC (μ * (2 * ‖ℓ‖))
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  change (2 * ‖ℓ‖)⁻¹ * ((1 + C) * (2 * R * (B ℓ * hypConst d M))) = _
  rw [mul_inv]
  ring

/-- Principal-value convergence for smooth decaying kernels with a support radius.
No convergence or integrability conclusion is assumed. -/
theorem tendsto_energyInvIntegral
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    Tendsto (fun μ => energyInvIntegral χ μ F) atTop
      (𝓝 (∫ ℓ, energyInvSliceLimit F ℓ)) := by
  obtain ⟨C, hC⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hCa : ∀ u, |χ u| ≤ C := by simpa only [Real.norm_eq_abs] using hC
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ℓ => (R * (1 + C) * hypConst d M) * (‖ℓ‖⁻¹ * B ℓ))
  · exact Eventually.of_forall fun μ =>
      (hF.stronglyMeasurable_energyInvInner hχ μ).aestronglyMeasurable
  · refine Eventually.of_forall fun μ => ?_
    filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    rw [Real.norm_eq_abs]
    exact abs_energyInvInner_le hF hgrad hDc hD hR hs hχ hCa μ hℓ
  · exact hgrad.integrable.const_mul _
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    exact tendsto_energyInvInner hF hgrad hDc hD hs hχ hℓ

/-- The outer integral at each finite scale is also integrable. -/
theorem integrable_energyInvInner
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) :
    Integrable (energyInvInner χ μ F) := by
  obtain ⟨C, hC⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hCa : ∀ u, |χ u| ≤ C := by simpa only [Real.norm_eq_abs] using hC
  refine (hgrad.integrable.const_mul (R * (1 + C) * hypConst d M)).mono'
    (hF.stronglyMeasurable_energyInvInner hχ μ).aestronglyMeasurable ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs]
  exact abs_energyInvInner_le hF hgrad hDc hD hR hs hχ hCa μ hℓ

/-- Existence is proved before introducing the principal-value definition. -/
theorem exists_energyInvIntegral_limit
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    ∃ v : ℝ, Tendsto (fun μ => energyInvIntegral χ μ F) atTop (𝓝 v) :=
  ⟨_, tendsto_energyInvIntegral hd hF hgrad hDc hD hR hs hχ⟩

/-- Principal value of the inverse energy resonance, defined from the proved
cutoff limit. The proof arguments specify a smooth decaying kernel with a support radius. -/
@[expose] noncomputable def energyPrincipalValue
    (F : Mom d → Mom d → ℝ) (D : Mom d → Mom d → Mom d →L[ℝ] ℝ)
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    (χ : ℝ → ℝ) (hχ : IsPVCutoff χ) : ℝ :=
  (exists_energyInvIntegral_limit hd hF hgrad hDc hD hR hs hχ).choose

/-- Characterization of the principal value, including the original cutoff limit. -/
theorem energyPrincipalValue_spec
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    Tendsto (fun μ => energyInvIntegral χ μ F) atTop
      (𝓝 (energyPrincipalValue F D hd hF hgrad hDc hD hR hs χ hχ)) :=
  (exists_energyInvIntegral_limit hd hF hgrad hDc hD hR hs hχ).choose_spec

/-- The value is the symmetric-quotient integral and hence independent of cutoff. -/
theorem energyPrincipalValue_eq_integral
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M R : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    (hR : 0 ≤ R) (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    energyPrincipalValue F D hd hF hgrad hDc hD hR hs χ hχ =
      ∫ ℓ, energyInvSliceLimit F ℓ :=
  tendsto_nhds_unique (energyPrincipalValue_spec hd hF hgrad hDc hD hR hs hχ)
    (tendsto_energyInvIntegral hd hF hgrad hDc hD hR hs hχ)

end WaveTurbulence
