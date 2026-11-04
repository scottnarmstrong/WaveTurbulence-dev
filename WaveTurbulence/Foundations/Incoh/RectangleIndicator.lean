/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothRectangle
public import WaveTurbulence.Foundations.Incoh.SmoothIntervalLimit

/-!
# Literal half-open rectangular time fibers

The smoothing sequence converges pointwise, with a common unit bound.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace WaveTurbulence.Incoh

/-- The literal tensor product of two half-open interval indicators. -/
@[expose] def rectangleIndicator (a b t : Fin 2 → ℝ) : ℂ :=
  (((Ioc (a 0) (b 0)).indicator (fun _ => (1 : ℝ)) (t 0) : ℝ) : ℂ) *
    (((Ioc (a 1) (b 1)).indicator (fun _ => (1 : ℝ)) (t 1) : ℝ) : ℂ)

theorem norm_smoothRectangle_le_one {ε : ℝ} (hε : 0 < ε)
    (a b t : Fin 2 → ℝ) (hab : a ≤ b) : ‖smoothRectangle ε a b t‖ ≤ 1 := by
  have hj (j : Fin 2) : ‖(smoothInterval ε (a j) (b j) (t j) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (smoothInterval_nonneg hε (hab j) _)]
    exact smoothInterval_le_one _ _ _ _
  rw [smoothRectangle, norm_mul]
  exact (mul_le_mul (hj 0) (hj 1) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem tendsto_smoothRectangle {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (a b : Fin 2 → ℝ) (hab : a ≤ b) (t : Fin 2 → ℝ) :
    Tendsto (fun n => smoothRectangle (ε n) a b t) atTop (𝓝 (rectangleIndicator a b t)) := by
  simpa only [smoothRectangle, rectangleIndicator, Function.comp_apply] using
    ((Complex.continuous_ofReal.tendsto _).comp (tendsto_smoothInterval hε hlim (hab 0) (t 0))).mul
    ((Complex.continuous_ofReal.tendsto _).comp (tendsto_smoothInterval hε hlim (hab 1) (t 1)))

end WaveTurbulence.Incoh
