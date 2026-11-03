/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearFourierLimit

/-!
# Joint-integral characterization of localized bilinear Fourier truncations

All finite truncations have continuous compactly supported integrands on the
product momentum space. The iterated integral therefore equals the joint
integral used in DH21 Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- A scalar resonance multiplier times a localized amplitude and Fourier phase. -/
@[expose] noncomputable def jointFourierIntegrand (g : ℝ → ℂ)
    (A : Mom d → Mom d → ℂ) (ξ η : Mom d) (p : Mom d × Mom d) : ℂ :=
  g ⟪p.1, p.2⟫_ℝ * (A p.1 p.2 * unitPhase 1 (⟪ξ, p.1⟫_ℝ + ⟪η, p.2⟫_ℝ))

/-- A localized amplitude is compactly supported on the product momentum space. -/
theorem hasCompactSupport_joint_amplitude
    {A : Mom d → Mom d → ℂ} {a b : Mom d} {R : ℝ}
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) :
    HasCompactSupport (Function.uncurry A) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall a R ×ˢ Metric.closedBall b R)
    ((isCompact_closedBall a R).prod (isCompact_closedBall b R))
  intro p hp
  by_contra hnot
  by_cases hx : p.1 ∈ Metric.closedBall a R
  · have hy : p.2 ∉ Metric.closedBall b R := fun hy => hnot ⟨hx, hy⟩
    exact hp (hsy p.1 p.2 (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hy))
  · exact hp (hsx p.1 p.2 (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx))

/-- Every continuous resonance multiplier gives an integrable localized joint integrand. -/
theorem integrable_jointFourierIntegrand
    {g : ℝ → ℂ} (hg : Continuous g) {A : Mom d → Mom d → ℂ}
    {a b : Mom d} {R : ℝ} (hA : Continuous (Function.uncurry A))
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    Integrable (jointFourierIntegrand g A ξ η) := by
  have hc : Continuous (jointFourierIntegrand g A ξ η) := by
    exact (hg.comp (continuous_fst.inner continuous_snd)).mul
      (hA.mul ((continuous_unitPhase 1).comp
        ((continuous_const.inner continuous_fst).add (continuous_const.inner continuous_snd))))
  apply hc.integrable_of_hasCompactSupport
  apply (hasCompactSupport_joint_amplitude hsx hsy).mono
  intro p hp hzero
  apply hp
  simp only [jointFourierIntegrand, Function.uncurry] at hzero ⊢
  rw [hzero, zero_mul, mul_zero]

/-- The finite bilinear Fourier truncation equals the joint integral of the source formula. -/
theorem bilinearFourierTruncation_eq_jointIntegral
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} {R : ℝ}
    (hA : Continuous (Function.uncurry A))
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    bilinearFourierTruncation χ μ A ξ η =
      ∫ p : Mom d × Mom d,
        jointFourierIntegrand (fun u => (((1 - χ (μ * u)) / u : ℝ) : ℂ)) A ξ η p := by
  have hi := integrable_jointFourierIntegrand
    (Complex.continuous_ofReal.comp (hχ.continuous_div μ)) hA hsx hsy ξ η
  rw [show (volume : Measure (Mom d × Mom d)) = volume.prod volume from rfl] at hi ⊢
  dsimp only [Function.comp_def] at hi
  rw [bilinearFourierTruncation, integral_prod _ hi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [bilinearInvFourierInner, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [jointFourierIntegrand, unitPhase_add]
  ring

end WaveTurbulence.Resonant
