/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Resonant.PVDecayBounds
public import WaveTurbulence.Foundations.Resonant.PVDecaySlices
public import WaveTurbulence.Foundations.Resonant.PrincipalValue

/-! # Principal-value characterization for decaying kernels

For TARGET (C.5) and Wave B2 REQUIRED F-5, polynomial decay of the kernel
and its gradient replaces compact support. Slice cancellation and two
applications of dominated convergence give the actual cutoff limit.
-/

public section
open MeasureTheory Filter Topology
open scoped NNReal
namespace WaveTurbulence.Resonant
variable {d : ℕ}

theorem tendsto_energyInvInner_of_decay
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Tendsto (fun μ => energyInvInner χ μ F ℓ) atTop (𝓝 (energyInvSliceLimit F ℓ)) := by
  have ht := hχ.tendsto_pvTruncation_of_lipschitz (integrable_sliceInt hF hℓ)
    (lipschitzWith_sliceInt hF hgrad hDc hD hℓ)
  have ha : 0 < 2*‖ℓ‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hℓ)
  have hscale : Tendsto (fun μ : ℝ => μ*(2*‖ℓ‖)) atTop atTop :=
    Tendsto.atTop_mul_const ha tendsto_id
  exact ((ht.comp hscale).const_mul (-(2*‖ℓ‖)⁻¹)).congr
    (fun μ => (energyInvInner_eq hF hχ μ hℓ).symm)

theorem abs_energyInvInner_le_of_decay
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M C : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hC : ∀ u, |χ u| ≤ C)
    (μ : ℝ) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    |energyInvInner χ μ F ℓ| ≤ (1+C)*
      (hypConst d M*(‖ℓ‖⁻¹*B ℓ)+(2⁻¹*hypConst (d+1) N)*(‖ℓ‖⁻¹*A ℓ)) := by
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hN : 0 ≤ 1+C := by linarith only [hCn]
  have hb := hχ.abs_pvTruncation_le_l1 (integrable_sliceInt hF hℓ)
    (lipschitzWith_sliceInt hF hgrad hDc hD hℓ) hC (μ*(2*‖ℓ‖))
  have hl1 : (∫ t, |sliceInt F ℓ t|) ≤ A ℓ*hypConst (d+1) N := by
    simpa only [Real.norm_eq_abs] using integral_norm_sliceInt_le hF hℓ
  have hb' : |pvTruncation χ (μ*(2*‖ℓ‖)) (sliceInt F ℓ)| ≤
      (1+C)*(2*(B ℓ*hypConst d M)+A ℓ*hypConst (d+1) N) :=
    hb.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2*(B ℓ*hypConst d M))) hl1) hN)
  rw [energyInvInner_eq hF hχ μ hℓ,abs_mul,abs_neg,abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hb' (by positivity)).trans_eq ?_
  rw [mul_inv]
  ring

/-- The actual inverse-energy cutoff converges for smooth kernels with
integrable polynomial decay in both the kernel and gradient, without a
support condition or assumed convergence estimate. -/
theorem tendsto_energyInvIntegral_of_decay
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) :
    Tendsto (fun μ => energyInvIntegral χ μ F) atTop (𝓝 (∫ ℓ, energyInvSliceLimit F ℓ)) := by
  obtain ⟨C,hC⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hCa : ∀ u, |χ u| ≤ C := by simpa only [Real.norm_eq_abs] using hC
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ℓ => (1+C)*(hypConst d M*(‖ℓ‖⁻¹*B ℓ)+(2⁻¹*hypConst (d+1) N)*(‖ℓ‖⁻¹*A ℓ)))
  · exact Eventually.of_forall fun μ => (stronglyMeasurable_energyInvInner hF hχ μ).aestronglyMeasurable
  · refine Eventually.of_forall fun μ => ?_
    filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    rw [Real.norm_eq_abs]
    exact abs_energyInvInner_le_of_decay hF hgrad hDc hD hχ hCa μ hℓ
  · exact ((hgrad.integrable.const_mul (hypConst d M)).add
      (hF.integrable.const_mul (2⁻¹*hypConst (d+1) N))).const_mul (1+C)
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    exact tendsto_energyInvInner_of_decay hF hgrad hDc hD hχ hℓ

end WaveTurbulence.Resonant
