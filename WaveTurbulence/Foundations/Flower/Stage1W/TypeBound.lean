/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # STAGE1W-GLUE G4: `Stage1TypeBoundFW` (R5), the weighted copy of main's `stage1_type_bound`.

`GPresented` weights are bounded by `cψ`, so the garden weight is bounded by `cψ^(#nodes)`; the weighted
decoration sums split over the piece partition, and `stage1_core_bound_int` is applied at size `cψ^(16N) s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-- A `GPresented` weight is bounded by its constant. -/
theorem GPresented.norm_le {d J : ℕ} {g : Mom d → ℂ} {c : ℝ} (h : GPresented J g c) (hc : 0 ≤ c) (x : Mom d) :
    ‖g x‖ ≤ c := by
  obtain ⟨α, _, M, hM, hv⟩ := h
  rw [← hv x]
  have h1 : ‖M.value x‖ ≤ ∫ a, ‖M.amplitude a‖ ∂M.μ := by
    unfold Cut2A.SpatialMeasure.value
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      M.amplitude_integrable.norm (Filter.Eventually.of_forall fun a => ?_)
    simp
  refine h1.trans ?_
  rw [integral_norm_eq_lintegral_enorm M.amplitude_integrable.aestronglyMeasurable]
  have h2 : ∫⁻ a, ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c := by
    refine le_trans (lintegral_mono fun a => ?_) hM
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      exact one_le_pow₀ (by linarith [norm_nonneg (M.frequency a)])
    calc ‖M.amplitude a‖ₑ = 1 * ‖M.amplitude a‖ₑ := (one_mul _).symm
      _ ≤ _ := by gcongr
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h2).trans (ENNReal.toReal_ofReal hc).le


end WaveTurbulence.Flower.Stage1W
