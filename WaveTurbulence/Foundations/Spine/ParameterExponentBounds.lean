/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentZeroNorm
/-! Uniform source exponent bounds, independent of the stage and later parameter choices. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem theta_le_two_eta_pow (P : WTParams) (p : ℕ) : P.theta p ≤ 2 * P.η ^ 20 := by
  have hh : ((2 : ℝ)⁻¹) ^ p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold WTParams.theta
  nlinarith [mul_nonneg (by positivity : 0 ≤ P.η ^ 20) (sub_nonneg.mpr hh)]

theorem exists_eta_exponent_reserve {a : ℝ} (ha : 0 < a) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
      Real.sqrt η ≤ a / 4 ∧ 2 * η ^ 20 ≤ a / 100 := by
  let η₀ := min 1 (min (a / 200) ((a / 4) ^ 2))
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη
  have hη1 : η ≤ 1 := hη.2.trans (min_le_left _ _)
  have hηa : η ≤ a / 200 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηsq : η ≤ (a / 4) ^ 2 := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · exact (Real.sqrt_le_iff).mpr ⟨by positivity, hηsq⟩
  · have hp : η ^ 20 ≤ η := by simpa using pow_le_pow_of_le_one hη.1.le hη1 (by decide : 1 ≤ 20)
    linarith

end WaveTurbulence.LGSpine
