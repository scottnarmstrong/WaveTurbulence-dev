/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ProductMeasureTools
public import Mathlib.Order.Interval.Set.Pi

/-!
# Finite-product Fubini with all coordinate intervals retained

Restriction of a finite product measure to a coordinate box is the
product of the restricted coordinate measures. This gives the exact
factor integrals used after grouped-time Tonelli.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- Independent nonnegative factors integrate exactly over a coordinate box. -/
theorem lintegral_fintype_prod_Icc {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, Preorder (E i)] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]
    (lo hi : (i : ι) → E i) (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x in Icc lo hi, ∏ i, f i (x i)) = ∏ i, ∫⁻ x in Icc (lo i) (hi i), f i x := by
  rw [volume_pi,← pi_univ_Icc,Measure.restrict_pi_pi]
  exact lintegral_fintype_prod_eq_prod ι f hf

end WaveTurbulence.Sumint
