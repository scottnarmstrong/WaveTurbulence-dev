/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ConstantAbsorption

/-!
# Strict exponent reserves with the exact sumint quantifier order

Any fixed coefficient, including one chosen after delta and the time labels,
is absorbed by a strict exponent reserve through the later lattice threshold.
The same threshold bounds three contributions and is independent of their
multiplicity. No estimate on the number of source vertices is needed here.
-/

public section

namespace WaveTurbulence.Sumint

/-- A fixed coefficient multiplying a smaller power is eventually bounded by the target power. -/
theorem exists_coefficient_power_le (K a b : ℝ) (hab : a < b) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, K*L^a ≤ L^b := by
  obtain ⟨R,hR,hbound⟩ := exists_constant_le_rpow K (sub_pos.mpr hab)
  refine ⟨R,hR,?_⟩
  intro L hL
  have hLp : 0 < L := by linarith [hR.trans hL]
  calc
    _ ≤ L^(b-a)*L^a := mul_le_mul_of_nonneg_right (hbound L hL) (Real.rpow_nonneg hLp.le _)
    _ = L^b := by rw [← Real.rpow_add hLp]; congr 1; ring

/-- One logarithm also costs only an arbitrarily small strict power reserve. -/
theorem exists_coefficient_log_power_le (K a b : ℝ) (hab : a < b) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, K*L^a*Real.log L ≤ L^b := by
  obtain ⟨R,hR,hbound⟩ := exists_constant_log_le_rpow K (sub_pos.mpr hab)
  refine ⟨R,hR,?_⟩
  intro L hL
  have hLp : 0 < L := by linarith [hR.trans hL]
  calc
    _ = (K*Real.log L)*L^a := by ring
    _ ≤ L^(b-a)*L^a := mul_le_mul_of_nonneg_right (hbound L hL) (Real.rpow_nonneg hLp.le _)
    _ = L^b := by rw [← Real.rpow_add hLp]; congr 1; ring

/-- Three nonlogarithmic contributions share one threshold, independently of multiplicity. -/
theorem exists_three_plain_power_sum_le (K₀ K₁ K₂ a₀ a₁ a₂ b : ℝ)
    (h₀ : a₀ < b) (h₁ : a₁ < b) (h₂ : a₂ < b) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      K₀*L^a₀+K₁*L^a₁+K₂*L^a₂ ≤ L^b := by
  obtain ⟨R₀,hR₀,hb₀⟩ := exists_coefficient_power_le (3*K₀) a₀ b h₀
  obtain ⟨R₁,hR₁,hb₁⟩ := exists_coefficient_power_le (3*K₁) a₁ b h₁
  obtain ⟨R₂,hR₂,hb₂⟩ := exists_coefficient_power_le (3*K₂) a₂ b h₂
  refine ⟨max R₀ (max R₁ R₂),hR₀.trans (le_max_left _ _),?_⟩
  intro L hL
  have h₀' := hb₀ L ((le_max_left _ _).trans hL)
  have h₁' := hb₁ L ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have h₂' := hb₂ L ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  linarith only [h₀',h₁',h₂']

/-- Three source contributions, the last logarithmic, share one later threshold. -/
theorem exists_three_power_sum_le (K₀ K₁ K₂ a₀ a₁ a₂ b : ℝ)
    (h₀ : a₀ < b) (h₁ : a₁ < b) (h₂ : a₂ < b) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      K₀*L^a₀+K₁*L^a₁+K₂*L^a₂*Real.log L ≤ L^b := by
  obtain ⟨R₀,hR₀,hb₀⟩ := exists_coefficient_power_le (3*K₀) a₀ b h₀
  obtain ⟨R₁,hR₁,hb₁⟩ := exists_coefficient_power_le (3*K₁) a₁ b h₁
  obtain ⟨R₂,hR₂,hb₂⟩ := exists_coefficient_log_power_le (3*K₂) a₂ b h₂
  refine ⟨max R₀ (max R₁ R₂),hR₀.trans (le_max_left _ _),?_⟩
  intro L hL
  have h₀' := hb₀ L ((le_max_left _ _).trans hL)
  have h₁' := hb₁ L ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have h₂' := hb₂ L ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  linarith only [h₀',h₁',h₂']

end WaveTurbulence.Sumint
