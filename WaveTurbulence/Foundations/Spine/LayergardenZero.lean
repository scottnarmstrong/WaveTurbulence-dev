/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ProperGardenZeroSum
public import WaveTurbulence.Foundations.Spine.CoupleZeroRemainder
public import WaveTurbulence.Foundations.Spine.OffDiagonal
/-! All three clauses of the exact B1.2 conclusion at branching order zero. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem layergarden_order_zero (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (p : ℕ) (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (t : ℝ) :
    (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
      ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
        ‖truncSum P (inputsF P R) (p + 1) 0 t ζ n‖ ≤
          jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
            P.δ ^ (2 * P.ν * 0)) ∧
    (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
      truncSum P (inputsF P R) (p + 1) 0 t ![1, -1] n = 0) ∧
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p 0 t) ≤
      ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm _ ζ _ n
    rw [truncSum_zero_of_proper P (inputsF P R) p (by omega) t ζ n, norm_zero]
    simp only [mul_zero, Real.rpow_zero, mul_one]
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)
      (Real.rpow_nonneg (zero_le_one.trans hL) _)
  · intro n hn
    exact truncSum_pair_off_diagonal P (inputsF P R) (p + 1) 0 t n hn
  · simpa only [mul_zero, Real.rpow_zero, mul_one] using
      coupleRemainder_zero_SNorm_bound P hd hL hp R hR t

end WaveTurbulence.LGSpine
