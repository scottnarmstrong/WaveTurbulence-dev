/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.NextRemainderBound
public import WaveTurbulence.Foundations.XChain.TaylorTailAbsorption
public import WaveTurbulence.Foundations.XChain.AnsatzInputFunctionBound
/-! The explicit next-remainder constant satisfies the actual ansatz target under numerical size conditions. -/
public section
namespace WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem nextRemainder_constant_le_target (P : WTParams) (p : ℕ)
    (hN : 4 ≤ P.N (p + 1)) (hL : 0 < P.L) (hC : 0 ≤ P.C₂)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1) (hre : P.C₁ * P.δ ≤ Real.exp (-1))
    (hθN : P.theta (p + 1) ≤ P.N (p + 1)) (hlog : Real.log P.L ≤ P.N (p + 1))
    (hAe : P.C₂ / (1 - P.C₁ * P.δ) ≤ Real.exp (P.N (p + 1) : ℝ))
    (hgap : 4 ≤ P.L ^ ((4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1))) :
    2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) +
      P.C₂ * (P.C₁ * P.δ) ^ (P.N (p + 1) ^ 4 / 2 + 1) / (1 - P.C₁ * P.δ) ≤
        P.L ^ (-P.theta (p + 1)) := by
  have hscale := two_power_le_half_of_gap hL hgap
  have hM : P.N (p + 1) ^ 4 ≤ 2 * (P.N (p + 1) ^ 4 / 2 + 1) := by omega
  have ht := geometric_taylor_tail_le_half_power hN hM hL (theta_nonneg P _) hθN hlog
    (div_nonneg hC (sub_pos.mpr hr1).le) hAe hr hre
  have he : P.C₂ * (P.C₁ * P.δ) ^ (P.N (p + 1) ^ 4 / 2 + 1) / (1 - P.C₁ * P.δ) =
      (P.C₂ / (1 - P.C₁ * P.δ)) * (P.C₁ * P.δ) ^ (P.N (p + 1) ^ 4 / 2 + 1) := by ring
  rw [he]
  have hs : -(4 * P.theta (p + 1) + P.theta p) / 5 = -((4 * P.theta (p + 1) + P.theta p) / 5) := by ring
  rw [hs]
  linarith

theorem nextRemainder_ansatz_SNormR_bound (P : WTParams) (hG : LayergardenBody P) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hδ : 0 < P.δ) (hC : 0 ≤ P.C₂)
    (hsmall : P.δ ^ (2 * P.ν) ≤ 1 / 2)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1) (hre : P.C₁ * P.δ ≤ Real.exp (-1))
    (hN : 4 ≤ P.N (p + 1)) (hθN : P.theta (p + 1) ≤ P.N (p + 1))
    (hlog : Real.log P.L ≤ P.N (p + 1))
    (hAe : P.C₂ / (1 - P.C₁ * P.δ) ≤ Real.exp (P.N (p + 1) : ℝ))
    (hgap : 4 ≤ P.L ^ ((4 * P.theta (p + 1) + P.theta p) / 5 - P.theta (p + 1)))
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    SNormR (P.Lambda (p + 1)) (P.Lambda (p + 1)) (nextRemainder P R p (P.N (p + 1) ^ 4) t) ≤
      ENNReal.ofReal (P.L ^ (-P.theta (p + 1))) := by
  exact (nextRemainder_SNormR_bound P hG hW R p hp hR hd hL hδ hC hsmall hr hr1
    (P.N (p + 1) ^ 4) le_rfl t ht).trans (ENNReal.ofReal_le_ofReal
      (nextRemainder_constant_le_target P p hN hL hC hr hr1 hre hθN hlog hAe hgap))

end WaveTurbulence.Induct
