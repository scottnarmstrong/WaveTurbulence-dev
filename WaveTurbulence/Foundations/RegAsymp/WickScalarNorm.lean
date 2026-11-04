/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.WickOrderBudget

/-! # Exact norm transport for normalized traced source sums -/

public section
namespace WaveTurbulence.RegAsymp

/-- Split the original normalization without dividing by the surviving
power; the identity includes empty surviving order and zero delta. -/
theorem norm_normalized_trace_product {q : ℝ} (hq : 0 ≤ q) (c z : ℂ)
    {n m r : ℕ} (h : m+r = n) :
    ‖((q^(2*n):ℝ):ℂ)*(c*z)‖ =
      ‖c‖*q^(2*r)*‖((q^(2*m):ℝ):ℂ)*z‖ := by
  have he : ((q^(2*n):ℝ):ℂ)*(c*z) =
      c*((q^(2*r):ℝ):ℂ)*(((q^(2*m):ℝ):ℂ)*z) := by
    simp only [Complex.ofReal_pow]
    rw [show 2*n=2*r+2*m by omega,pow_add]
    ring
  rw [he,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hq _)]

end WaveTurbulence.RegAsymp
