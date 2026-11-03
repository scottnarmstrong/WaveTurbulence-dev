/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Bounding ordered integrals by integrals over a fixed box

The ordering constraints may be discarded after taking absolute values.
The proof keeps oriented integrals, including reversed time endpoints,
and does not impose extra integrability hypotheses on their amplitudes.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Nonnegative integration over a coordinate box, in the same recursive coordinate order. -/
@[expose] noncomputable def boxIntegral : (n : ℕ) → ((Fin n → ℝ) → ℝ≥0∞) → ℝ → ℝ≥0∞
  | 0, f, _ => f Fin.elim0
  | n + 1, f, R => ∫⁻ u in Icc (-R) R, boxIntegral n (fun v => f (Fin.cons u v)) R

/-- Absolute value of an oriented interval integral is bounded on its unoriented interval. -/
theorem enorm_intervalIntegral_le (f : ℝ → ℂ) (s t : ℝ) :
    ‖∫ u in s..t, f u‖ₑ ≤ ∫⁻ u in uIoc s t, ‖f u‖ₑ := by
  rcases le_total s t with hst | hts
  · rw [intervalIntegral.integral_of_le hst, uIoc_of_le hst]
    exact enorm_integral_le_lintegral_enorm _
  · rw [intervalIntegral.integral_of_ge hts, uIoc_of_ge hts, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _

/-- Discarding the simplex ordering gives a uniform box bound. -/
theorem enorm_orderedIntegral_le_boxIntegral (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (R t s : ℝ) (ht : t ∈ Icc (-R) R) (hs : s ∈ Icc (-R) R) :
    ‖orderedIntegral n F t s‖ₑ ≤ boxIntegral n (fun v => ‖F v‖ₑ) R := by
  induction n generalizing t s with
  | zero => exact le_rfl
  | succ n ih =>
    change ‖∫ u in s..t, orderedIntegral n (fun v => F (Fin.cons u v)) u s‖ₑ ≤
      ∫⁻ u in Icc (-R) R, boxIntegral n (fun v => ‖F (Fin.cons u v)‖ₑ) R
    have hsub : uIoc s t ⊆ Icc (-R) R :=
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht))
    calc
      _ ≤ ∫⁻ u in uIoc s t, ‖orderedIntegral n (fun v => F (Fin.cons u v)) u s‖ₑ :=
        enorm_intervalIntegral_le _ s t
      _ ≤ ∫⁻ u in uIoc s t, boxIntegral n (fun v => ‖F (Fin.cons u v)‖ₑ) R := by
        apply setLIntegral_mono' measurableSet_uIoc
        intro u hu
        exact ih _ u s (hsub hu) hs
      _ ≤ _ := lintegral_mono_set hsub

end WaveTurbulence.Fourier
