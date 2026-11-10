/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral
public import WaveTurbulence.Foundations.Fourier.EndpointCutoffBounds
public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
import Mathlib.Tactic

/-!
# Support and absolute-value bounds from the two output cutoffs

These bounds apply equally to every boundary face of an ordered integral.
Only the endpoint factors are used to localize the output time variables.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal ContDiff

namespace WaveTurbulence.Fourier

/-- Membership in the fixed two-time coordinate box. -/
theorem mem_two_time_box_iff (R : ℝ) (t : Fin 2 → ℝ) :
    t ∈ Icc (fun _ : Fin 2 => -R) (fun _ => R) ↔ |t 0| ≤ R ∧ |t 1| ≤ R := by
  simp only [Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, abs_le]
  tauto

/-- Two cutoff factors kill every output outside the fixed time box. -/
theorem endpoint_product_eq_zero_outside {a b : ℝ → ℝ} {R C : ℝ}
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (t : Fin 2 → ℝ) (ht : t ∉ Icc (fun _ : Fin 2 => -R) (fun _ => R)) :
    (a (t 0) : ℂ) * (b (t 1) : ℂ) = 0 := by
  by_cases h0 : |t 0| ≤ R
  · have h1 : R < |t 1| := lt_of_not_ge (fun h => ht ((mem_two_time_box_iff R t).mpr ⟨h0, h⟩))
    simp [hb.eq_zero _ h1]
  · simp [ha.eq_zero _ (lt_of_not_ge h0)]

/-- The product of two bounded endpoint factors is bounded by the squared common bound. -/
theorem norm_endpoint_product_le {a b : ℝ → ℝ} {R C : ℝ} (hC : 0 ≤ C)
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C) (t : Fin 2 → ℝ) :
    ‖(a (t 0) : ℂ) * (b (t 1) : ℂ)‖ ≤ C ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa only [pow_two] using mul_le_mul (ha.abs_le _) (hb.abs_le _) (abs_nonneg _) hC

/-- Output cutoff localization, independent of the ordered amplitude. -/
theorem weightedOrderedIntegral_hasCompactSupport {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (A : (Fin n → ℝ) → ℂ) : HasCompactSupport (weightedOrderedIntegral n a b A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := fun _ : Fin 2 => -R) (b := fun _ => R))
  intro t ht
  rw [weightedOrderedIntegral, endpoint_product_eq_zero_outside ha hb t ht, zero_mul]

end WaveTurbulence.Fourier
