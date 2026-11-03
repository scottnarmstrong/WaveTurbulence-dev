/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BoxIntegralTonelli
import Mathlib.Tactic

/-!
# Addition in nonnegative coordinate box integrals

A measurable summand can be split off at every recursive integration.
This is used for the cutoff and source pieces of a diagonal amplitude derivative.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Box integration distributes over addition when the first summand is measurable. -/
theorem boxIntegral_add (n : ℕ) {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (g : (Fin n → ℝ) → ℝ≥0∞) (R : ℝ) :
    boxIntegral n (fun v => f v + g v) R = boxIntegral n f R + boxIntegral n g R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫⁻ u in Icc (-R) R, boxIntegral n (fun v => f (Fin.cons u v) + g (Fin.cons u v)) R) = _
    have he (u : ℝ) := ih (f := fun v => f (Fin.cons u v))
      (hf.comp ((measurable_fin_cons n).comp (measurable_const.prodMk measurable_id)))
      (fun v => g (Fin.cons u v))
    simp_rw [he]
    have hm := measurable_boxIntegral_parameter n R
      (f := fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) (hf.comp (measurable_fin_cons n))
    exact lintegral_add_left hm _

end WaveTurbulence.Fourier
