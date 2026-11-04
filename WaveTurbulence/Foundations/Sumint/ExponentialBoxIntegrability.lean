/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ExponentialBoxFourier
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Time-integrability guard for the explicit rectangular kernel

The finite interval factor is integrable by continuity. The two negative
half-line factors have exponential decay. These are genuine integrable
ambient functions, as required by the exact draft norm guard.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- Every finite-interval exponential factor is integrable. -/
theorem integrable_exponentialInterval_Icc (a b σ : ℝ) :
    Integrable (exponentialInterval (Icc a b) σ) := by
  have hc : Continuous (fun t : ℝ => (Real.exp (σ*t) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hi : IntegrableOn (fun t : ℝ => (Real.exp (σ*t) : ℂ)) (Icc a b) := hc.integrableOn_Icc
  exact hi.integrable_indicator measurableSet_Icc

/-- The negative half-line factor has an integrable exponential tail. -/
theorem integrable_exponentialInterval_Iio (u : ℝ) :
    Integrable (exponentialInterval (Iio u) 1) := by
  have hi := (integrableOn_exp_mul_complex_Iic (a := 1) (by norm_num) u).mono_set
    (show Iio u ⊆ Iic u from fun _ h => h.le)
  have he : (fun t : ℝ => Complex.exp ((1 : ℂ)*t)) =
      fun t : ℝ => (Real.exp (1*t) : ℂ) := by
    funext t
    simp only [one_mul, Complex.ofReal_exp]
  rw [he] at hi
  exact hi.integrable_indicator measurableSet_Iio

/-- The explicit three-time rectangular kernel satisfies the exact ambient integrability requirement. -/
theorem integrable_exponentialBox (a b u : ℝ) : Integrable (exponentialBox a b u) := by
  have hf (j : Fin 3) : Integrable
      (![exponentialInterval (Icc a b) (-1), exponentialInterval (Iio u) 1,
        exponentialInterval (Iio u) 1] j) := by
    fin_cases j
    · exact integrable_exponentialInterval_Icc a b (-1)
    · exact integrable_exponentialInterval_Iio u
    · exact integrable_exponentialInterval_Iio u
  change Integrable (fun t : Fin 3 → ℝ => ∏ j,
    (![exponentialInterval (Icc a b) (-1), exponentialInterval (Iio u) 1,
      exponentialInterval (Iio u) 1] j) (t j))
  simpa only [volume_pi] using
    Integrable.fintype_prod (μ := fun _ : Fin 3 => (volume : Measure ℝ)) hf

end WaveTurbulence.Sumint
