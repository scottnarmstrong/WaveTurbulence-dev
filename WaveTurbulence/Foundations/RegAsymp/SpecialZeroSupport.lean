/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Statement

/-! # Special profile factors annihilate zero-energy coordinate slices -/

public section
namespace WaveTurbulence.RegAsymp
open ApproxNT

/-- A special energy equal to zero annihilates the literal source profile. -/
theorem resProfile_eq_zero_of_coordinate_zero {n : ℕ} (J : Finset (Fin n))
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (Ω : Fin n → ℝ) {j : Fin n}
    (hj : j ∈ J) (hΩ : Ω j = 0) : resProfile J Ψ Ω = 0 := by
  classical
  unfold resProfile
  have hp : (∏ i ∈ J, ((Fourier.chiInfinity (Ω i)/Ω i:ℝ):ℂ)) = 0 := by
    apply Finset.prod_eq_zero hj
    rw [hΩ,div_zero,Complex.ofReal_zero]
  rw [hp,zero_mul]

end WaveTurbulence.RegAsymp
