/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TimeFactorCoordinates

/-!
# Nonnegative Fubini in the exact source time coordinates

Regrouping the actual Lebesgue measure, followed by finite-product
Fubini, separates independent linear, pair and normal time factors.
The functions may include their own interval indicators and nonnegative
case multipliers; no interval volume constant is inserted here.
-/

public section

open MeasureTheory ENNReal

namespace WaveTurbulence.Sumint

/-- Exact nonnegative factorization in the draft's time-coordinate measure. -/
theorem lintegral_time_factor_product (S : SumintShape)
    (f : (a : FactorIdx S) → (FactorCoordinate S a → ℝ) → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) :
    (∫⁻ τ : S.TVar → ℝ, ∏ a : FactorIdx S, f a (timeCoordinateGrouping S τ a)) =
      ∏ a : FactorIdx S, ∫⁻ z : FactorCoordinate S a → ℝ, f a z := by
  have h := (volume_preserving_timeCoordinateGrouping S).lintegral_comp_emb
    (timeCoordinateGrouping S).measurableEmbedding
    (fun z => ∏ a : FactorIdx S, f a (z a))
  rw [h]
  exact lintegral_fintype_prod_eq_prod (FactorIdx S) f hf

/-- Any nonnegative integrand dominated by separated time factors inherits their product bound. -/
theorem lintegral_le_time_factor_product (S : SumintShape)
    (g : (S.TVar → ℝ) → ℝ≥0∞)
    (f : (a : FactorIdx S) → (FactorCoordinate S a → ℝ) → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a))
    (hgf : ∀ τ, g τ ≤ ∏ a : FactorIdx S, f a (timeCoordinateGrouping S τ a)) :
    (∫⁻ τ, g τ) ≤ ∏ a : FactorIdx S, ∫⁻ z : FactorCoordinate S a → ℝ, f a z := by
  exact (lintegral_mono hgf).trans_eq (lintegral_time_factor_product S f hf)

end WaveTurbulence.Sumint
