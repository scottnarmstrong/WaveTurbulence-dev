/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.MinorArcExponents

/-! # Physical scale identities in the shared-vertex reduction -/

public section
namespace WaveTurbulence.WeylSums

/-- Combine the lattice prefactor, two-time Jacobian, Weyl moment scale,
and normalized upper time into one exact power of `L`. -/
theorem cubic_star_physical_scale {L T₀ : ℝ} (hL : 0 < L) (hT₀ : 0 ≤ T₀)
    (d : ℕ) (γ r q : ℝ) :
    L^(2*d)*(4*L^2)^2*(12*L)^r*(T₀*L^(2*γ)/(4*L^2))^q =
      (16*(12 : ℝ)^r*(T₀/4)^q)*L^(2*(d : ℝ)+4+r+(2*γ-2)*q) := by
  have hLnat : L^(2*d) = L^(2*(d : ℝ)) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hJac : (4*L^2)^2 = 16*L^(4 : ℝ) := by rw [show L^(4 : ℝ) = L^4 by norm_cast]; ring
  rw [hLnat,hJac,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hL.le,
    upper_time_window_power hL,Real.mul_rpow (by positivity : (0 : ℝ) ≤ T₀/4) (by positivity),
    ← Real.rpow_mul hL.le]
  calc
    _ = (16*(12 : ℝ)^r*(T₀/4)^q)*
        (L^(2*(d : ℝ))*L^(4 : ℝ)*L^r*L^((2*γ-2)*q)) := by ring
    _ = _ := by rw [← Real.rpow_add hL,← Real.rpow_add hL,← Real.rpow_add hL]

end WaveTurbulence.WeylSums
