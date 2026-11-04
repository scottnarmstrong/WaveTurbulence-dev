/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BoxProductIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pair-box integrals in the two time coordinates

The native product-space box and the iterated outer/inner time
integrals are exactly identified. For a continuous nonnegative
integrand the real and nonnegative forms agree as well.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- A pair order interval is the product of its two scalar intervals. -/
theorem pair_Icc_eq_product (a b l u : ℝ) : Icc (a,l) (b,u) = Icc a b ×ˢ Icc l u := by
  ext z
  simp only [mem_Icc,Prod.le_def,mem_prod]
  tauto

/-- Exact nonnegative Fubini on a pair-time box. -/
theorem lintegral_pair_Icc (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) (a b l u : ℝ) :
    (∫⁻ z in Icc (a,l) (b,u), f z) = ∫⁻ t in Icc a b, ∫⁻ s in Icc l u, f (t,s) := by
  rw [pair_Icc_eq_product,Measure.volume_eq_prod,← Measure.prod_restrict]
  exact lintegral_prod _ hf.aemeasurable

/-- Real and nonnegative iterated pair-box integrals agree for continuous nonnegative factors. -/
theorem ofReal_integral_pair_Icc (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ z, 0 ≤ f z) (a b l u : ℝ) :
    ENNReal.ofReal (∫ t in Icc a b, ∫ s in Icc l u, f (t,s)) =
      ∫⁻ z in Icc (a,l) (b,u), ENNReal.ofReal (f z) := by
  have hi : IntegrableOn f (Icc a b ×ˢ Icc l u) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have he : (∫ z in Icc a b ×ˢ Icc l u, f z) = ∫ t in Icc a b, ∫ s in Icc l u, f (t,s) := by
    rw [Measure.volume_eq_prod] at hi ⊢
    exact setIntegral_prod f hi
  rw [← he,pair_Icc_eq_product]
  exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)

end WaveTurbulence.Sumint
