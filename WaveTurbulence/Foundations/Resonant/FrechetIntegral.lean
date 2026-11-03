/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.DualCoordinates
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fréchet differentiation under the resonant integral

Moving-hyperplane integrals of derivative functionals are measurable and
integrable because their finite scalar basis evaluations are delta kernels.
This supplies all hypotheses for differentiation at both integration levels.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- The derivative functional integrated over the resonance hyperplane. -/
@[expose] noncomputable def deltaFDerivIntegral (G : Mom d → Mom d → H →L[ℝ] ℝ) : H →L[ℝ] ℝ :=
  ∫ ℓ : Mom d, (2 * ‖ℓ‖)⁻¹ • ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G ℓ w

omit [FiniteDimensional ℝ H] in
/-- Evaluation of a decaying derivative functional is a scalar delta kernel. -/
theorem deltaKernel_clm_apply
    {G : Mom d → Mom d → H →L[ℝ] ℝ} {B : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hG : DeltaKernel (fun ℓ x => ‖G ℓ x‖) B b M)
    (hc : Continuous (Function.uncurry G)) (v : H) :
    DeltaKernel (fun ℓ x => G ℓ x v) (fun ℓ => ‖v‖ * B ℓ) b M where
  cont := hc.clm_apply continuous_const
  bound ℓ x := by
    calc |G ℓ x v| ≤ ‖G ℓ x‖ * ‖v‖ := by
          simpa only [Real.norm_eq_abs] using (G ℓ x).le_opNorm v
      _ ≤ (B ℓ * (1 + ‖b ℓ + x‖) ^ (-M)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (by simpa only [abs_of_nonneg (norm_nonneg _)] using hG.bound ℓ x) (norm_nonneg _)
      _ = _ := by ring
  dim := hG.dim
  integrable := by
    simpa only [mul_left_comm _ ‖v‖] using hG.integrable.const_mul ‖v‖

/-- The inner derivative-functional integral is a genuine Bochner integral. -/
theorem integrable_clm_perp
    {G : Mom d → Mom d → H →L[ℝ] ℝ} {B : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hG : DeltaKernel (fun ℓ x => ‖G ℓ x‖) B b M)
    (hc : Continuous (Function.uncurry G)) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => G ℓ w) := by
  refine (hG.integrable_slice_dom hℓ).mono'
    (hc.comp (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  simpa only [abs_of_nonneg (norm_nonneg _), zero_smul, zero_add] using hG.slice_bound hℓ 0 w

/-- The outer derivative-functional integral is integrable by finite basis reconstruction. -/
theorem integrable_clm_outer
    {G : Mom d → Mom d → H →L[ℝ] ℝ} {B : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hG : DeltaKernel (fun ℓ x => ‖G ℓ x‖) B b M)
    (hc : Continuous (Function.uncurry G)) (hd : 0 < d) :
    Integrable (fun ℓ : Mom d => (2 * ‖ℓ‖)⁻¹ • ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G ℓ w) := by
  apply integrable_clm_of_basis (Module.finBasis ℝ H)
  intro i
  have hi := (deltaKernel_clm_apply hG hc ((Module.finBasis ℝ H) i)).integrable_outer hd
  refine hi.congr ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [smul_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (integrable_clm_perp hG hc hℓ)]

/-- Evaluation commutes with both levels of the derivative integral. -/
theorem deltaFDerivIntegral_apply
    {G : Mom d → Mom d → H →L[ℝ] ℝ} {B : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hG : DeltaKernel (fun ℓ x => ‖G ℓ x‖) B b M)
    (hc : Continuous (Function.uncurry G)) (hd : 0 < d) (v : H) :
    deltaFDerivIntegral G v = deltaInt (fun ℓ x => G ℓ x v) := by
  rw [deltaFDerivIntegral, ContinuousLinearMap.integral_apply (integrable_clm_outer hG hc hd)]
  unfold deltaInt
  refine integral_congr_ae ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [smul_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (integrable_clm_perp hG hc hℓ)]

omit [FiniteDimensional ℝ H] in
/-- A uniform norm bound for the outer derivative integrand. -/
theorem norm_clm_outer_le
    {G : Mom d → Mom d → H →L[ℝ] ℝ} {B : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hG : DeltaKernel (fun ℓ x => ‖G ℓ x‖) B b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    ‖(2 * ‖ℓ‖)⁻¹ • ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G ℓ w‖ ≤
      (2⁻¹ * hypConst d M) * (‖ℓ‖⁻¹ * B ℓ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hi := norm_integral_le_integral_norm (μ := volume) (fun w : ↥(ℝ ∙ ℓ)ᗮ => G ℓ w)
  have hb := hG.abs_sliceInt_le hℓ 0
  simp only [sliceInt, zero_smul, zero_add] at hb
  have hh := hi.trans ((le_abs_self _).trans hb)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by rw [mul_inv]; ring)

/-- Local dominated Fréchet differentiation in an arbitrary finite-dimensional
parameter space, with all measurability and integrability obligations discharged. -/
theorem hasFDerivAt_deltaInt_of_local_decay
    {F : H → Mom d → Mom d → ℝ} {G : H → Mom d → Mom d → H →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ} {U : Set H}
    (hU : IsOpen U) (hd : 0 < d)
    (hF : ∀ k ∈ U, DeltaKernel (F k) A a N)
    (hG : ∀ k ∈ U, DeltaKernel (fun ℓ x => ‖G k ℓ x‖) B b M)
    (hGc : ∀ k ∈ U, Continuous (Function.uncurry (G k)))
    (hD : ∀ k ∈ U, ∀ ℓ x, HasFDerivAt (fun p => F p ℓ x) (G k ℓ x) k)
    {k : H} (hk : k ∈ U) :
    HasFDerivAt (fun p => deltaInt (F p)) (deltaFDerivIntegral (G k)) k := by
  have hinner : ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ p ∈ U,
      HasFDerivAt (fun q => ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F q ℓ w)
        (∫ w : ↥(ℝ ∙ ℓ)ᗮ, G p ℓ w) p := by
    intro ℓ hℓ p hp
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := U)
      (F := fun q (w : ↥(ℝ ∙ ℓ)ᗮ) => F q ℓ w)
      (F' := fun q (w : ↥(ℝ ∙ ℓ)ᗮ) => G q ℓ w) (hU.mem_nhds hp)
    · filter_upwards [hU.mem_nhds hp] with q hq
      simpa only [zero_smul, zero_add] using ((hF q hq).continuous_slice ℓ 0).aestronglyMeasurable
    · exact (hF p hp).integrable_perp hℓ
    · exact ((hGc p hp).comp (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable
    · refine Eventually.of_forall fun w q hq => ?_
      simpa only [abs_of_nonneg (norm_nonneg _), zero_smul, zero_add] using (hG q hq).slice_bound hℓ 0 w
    · exact (hG p hp).integrable_slice_dom hℓ
    · exact Eventually.of_forall fun w q hq => hD q hq ℓ w
  unfold deltaInt deltaFDerivIntegral
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := U)
    (F := fun p (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F p ℓ w)
    (F' := fun p (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ • ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G p ℓ w) (hU.mem_nhds hk)
  · filter_upwards [hU.mem_nhds hk] with p hp
    exact ((hF p hp).integrable_outer hd).aestronglyMeasurable
  · exact (hF k hk).integrable_outer hd
  · exact (integrable_clm_outer (hG k hk) (hGc k hk) hd).aestronglyMeasurable
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro p hp
    exact norm_clm_outer_le (hG p hp) hℓ
  · exact (hG k hk).integrable.const_mul (2⁻¹ * hypConst d M)
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro p hp
    have hh := (hinner ℓ hℓ p hp).const_smul ((2 * ‖ℓ‖)⁻¹)
    have he : ((2 * ‖ℓ‖)⁻¹ • (fun q => ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F q ℓ w)) =
        (fun q => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F q ℓ w) := by
      funext q
      exact smul_eq_mul _ _
    rw [he] at hh
    exact hh

end WaveTurbulence.Resonant
