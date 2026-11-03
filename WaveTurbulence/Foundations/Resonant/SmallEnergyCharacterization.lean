/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.JointFourierIntegral

/-!
# Principal-value interpretation of the low-energy cutoff

DH21 Lemma 6.3(2) uses `χ₀(μΩ)/Ω`. Its principal value is the full limit minus
the finite high-energy truncation. We prove this by introducing a second
cutoff `χ∞(νΩ)` and passing to `ν→∞` in the joint integral.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- A second cutoff removes the pole in the source's low-energy expression. -/
@[expose] noncomputable def lowBilinearFourierTruncation (χ : ℝ → ℝ) (ν μ : ℝ)
    (A : Mom d → Mom d → ℂ) (ξ η : Mom d) : ℂ :=
  ∫ p : Mom d × Mom d, jointFourierIntegrand
    (fun u => (((1 - χ (ν * u)) / u : ℝ) : ℂ) * (χ (μ * u) : ℂ)) A ξ η p

/-- Algebraic subtraction identity at finite cutoff scales. -/
theorem lowBilinearFourierTruncation_eq
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (ν μ : ℝ)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} {R : ℝ}
    (hA : Continuous (Function.uncurry A))
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    lowBilinearFourierTruncation χ ν μ A ξ η = bilinearFourierTruncation χ ν A ξ η -
      ∫ p : Mom d × Mom d, (1 - χ (ν * ⟪p.1, p.2⟫_ℝ) : ℝ) *
        jointFourierIntegrand (fun u => (((1 - χ (μ * u)) / u : ℝ) : ℂ)) A ξ η p := by
  have hi1 := integrable_jointFourierIntegrand
    (Complex.continuous_ofReal.comp (hχ.continuous_div ν)) hA hsx hsy ξ η
  dsimp only [Function.comp_def] at hi1
  have hi2 : Integrable (fun p : Mom d × Mom d =>
      ((1 - χ (ν * ⟪p.1, p.2⟫_ℝ) : ℝ) : ℂ) *
        jointFourierIntegrand (fun u => (((1 - χ (μ * u)) / u : ℝ) : ℂ)) A ξ η p) := by
    have hgc : Continuous (fun u : ℝ => ((1 - χ (ν * u) : ℝ) : ℂ) *
        (((1 - χ (μ * u)) / u : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id)))).mul
        (Complex.continuous_ofReal.comp (hχ.continuous_div μ))
    have hh := integrable_jointFourierIntegrand hgc hA hsx hsy ξ η
    exact hh.congr (Eventually.of_forall fun p => by dsimp [jointFourierIntegrand]; ring)
  rw [lowBilinearFourierTruncation, bilinearFourierTruncation_eq_jointIntegral hχ ν hA hsx hsy ξ η,
    ← integral_sub hi1 hi2]
  congr 1
  funext p
  simp only [jointFourierIntegrand, div_eq_mul_inv]
  push_cast
  ring

/-- The cross term is absolutely integrable and converges to the finite truncation. -/
theorem tendsto_jointHighCross
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} {R : ℝ}
    (hA : Continuous (Function.uncurry A))
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    Tendsto (fun ν : ℝ => ∫ p : Mom d × Mom d,
      ((1 - χ (ν * ⟪p.1, p.2⟫_ℝ) : ℝ) : ℂ) *
        jointFourierIntegrand (fun u => (((1 - χ (μ * u)) / u : ℝ) : ℂ)) A ξ η p)
      atTop (𝓝 (bilinearFourierTruncation χ μ A ξ η)) := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  let f := jointFourierIntegrand (fun u => (((1 - χ (μ * u)) / u : ℝ) : ℂ)) A ξ η
  have hi : Integrable f := integrable_jointFourierIntegrand
    (Complex.continuous_ofReal.comp (hχ.continuous_div μ)) hA hsx hsy ξ η
  rw [bilinearFourierTruncation_eq_jointIntegral hχ μ hA hsx hsy ξ η]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => (1 + C) * ‖f p‖) ?_ ?_ (hi.norm.const_mul _) ?_
  · exact Eventually.of_forall fun ν =>
      (Complex.continuous_ofReal.comp
        (continuous_const.sub (hχ.cont.comp
          (continuous_const.mul (continuous_fst.inner continuous_snd))))).aestronglyMeasurable.mul
            hi.aestronglyMeasurable
  · refine Eventually.of_forall fun ν => Eventually.of_forall fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (ν * ⟪p.1, p.2⟫_ℝ)) 1)) (norm_nonneg _)
  · refine Eventually.of_forall fun p => ?_
    by_cases hp : ⟪p.1, p.2⟫_ℝ = 0
    · have hz : f p = 0 := by simp [f, jointFourierIntegrand, hp]
      change Tendsto (fun ν : ℝ => ((1 - χ (ν * ⟪p.1, p.2⟫_ℝ) : ℝ) : ℂ) * f p) atTop (𝓝 (f p))
      simp only [hz, mul_zero]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hχ.eventually_comp_eq_zero hp] with ν hν
      simp only [hν, sub_zero, Complex.ofReal_one, one_mul]

/-- Full principal-value characterization of the low-energy expression. -/
theorem tendsto_lowBilinearFourierTruncation
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (μ : ℝ) (ξ η : Mom d) :
    Tendsto (fun ν => lowBilinearFourierTruncation χ ν μ A ξ η) atTop
      (𝓝 (bilinearFourierLimitFormula A ξ η - bilinearFourierTruncation χ μ A ξ η)) := by
  have ht := (tendsto_bilinearFourierTruncation hd hχ hχs hC hR hA hL hb hsx hsy ξ η).sub
    (tendsto_jointHighCross hχ μ hA hsx hsy ξ η)
  exact ht.congr fun ν => (lowBilinearFourierTruncation_eq hχ ν μ hA hsx hsy ξ η).symm

end WaveTurbulence.Resonant
