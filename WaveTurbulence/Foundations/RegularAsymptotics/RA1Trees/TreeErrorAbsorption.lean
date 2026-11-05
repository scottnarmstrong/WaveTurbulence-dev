/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeGeometricBudget

/-! # The complete explicit tree error budget has the required geometric delta dependence -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open scoped ENNReal

/-- Fixed root/input/time constants,2^n coefficient subsets, geometric envelope mass,
and the actual9^n row loss combine into C*(C*delta)^n without order-cutoff dependence. -/
theorem tree_error_budget_absorption {a b c p e k D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (he : 0 ≤ e) (hk : 0 ≤ k) (hD : 0 ≤ D) (H : ℝ≥0∞) (hH : H < ⊤) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∀ δ x r : ℝ, 0 ≤ δ → 0 ≤ x → x ≤ (9:ℝ)^n → 0 ≤ r →
      (ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (c^n)*ENNReal.ofReal p^(2*n+1)))) *
        (H*(ENNReal.ofReal (e*(k*δ)^n*x)*((2:ℝ≥0∞)^n*(ENNReal.ofReal r*(2*ENNReal.ofReal D^n))))) ≤
          ENNReal.ofReal (C*(C*δ)^n*r) := by
  obtain ⟨C,hC,hbound⟩ := exists_common_geometric_bound
    (2*a*b*p*H.toReal*e) (c*p^2*k*9*2*D)
  refine ⟨C,hC,?_⟩
  intro n δ x r hδ hx hx9 hr
  have hHr : 0 ≤ H.toReal := ENNReal.toReal_nonneg
  have hHeq : H=ENNReal.ofReal H.toReal := (ENNReal.ofReal_toReal hH.ne).symm
  rw [hHeq]
  have heq : (ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (c^n)*ENNReal.ofReal p^(2*n+1)))) *
      (ENNReal.ofReal H.toReal*(ENNReal.ofReal (e*(k*δ)^n*x)*
        ((2:ℝ≥0∞)^n*(ENNReal.ofReal r*(2*ENNReal.ofReal D^n))))) =
      ENNReal.ofReal (a*(b*(c^n*p^(2*n+1)))*
        (H.toReal*(e*(k*δ)^n*x)*((2:ℝ)^n*(r*(2*D^n))))) := by
    simp (disch := positivity) only [ENNReal.ofReal_mul,ENNReal.ofReal_pow,ENNReal.ofReal_ofNat]
    ring
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  have hbudget := tree_spatial_budget_le_geometric ha hb hc hp he (mul_nonneg hk hδ)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1) n hx9
  calc
    _ = (a*(b*(c^n*p^(2*n+1)))*(e*((k*δ)^n*1^n*1^(2*n))*x))*
        (H.toReal*((2:ℝ)^n*(r*(2*D^n)))) := by simp only [one_pow,mul_one]; ring
    _ ≤ ((a*b*p*e)*(c*p^2*(k*δ)*1*1^2*9)^n)*
        (H.toReal*((2:ℝ)^n*(r*(2*D^n)))) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ((2*a*b*p*H.toReal*e)*(c*p^2*k*9*2*D)^n)*δ^n*r := by
      simp only [one_pow,mul_one,mul_pow]
      ring
    _ ≤ (C*C^n)*δ^n*r := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound n) (by positivity)) hr
    _ = _ := by rw [mul_pow]; ring

end WaveTurbulence.RegAsymp
