/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.Absorption

/-!
# G10 with the source induction exponents

The final exponent is `θ=η^20`, fixed before the profile, terminal time,
and subdivision length. The large-size threshold is chosen afterward and
necessarily depends on the smallest induction gap `η^20 2^(-D)`.
No unfrozen Wave B record or definition is imported.
-/

public section

namespace WaveTurbulence.MainGlue

/-- The induction exponent has a positive gap uniform over all steps up to `D`. -/
theorem induction_exponent_gap {η : ℝ} (hη : 0 < η) (D : ℕ) :
    0 < η ^ 20 * (2 : ℝ)⁻¹ ^ D ∧ ∀ p ≤ D,
      η ^ 20 + η ^ 20 * (2 : ℝ)⁻¹ ^ D ≤ η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ p) := by
  refine ⟨mul_pos (pow_pos hη _) (pow_pos (by norm_num) _), ?_⟩
  intro p hp
  have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hp
  calc
    _ = η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hpow) (pow_nonneg hη.le _)

/-- G10(c), uniform over the entire finite induction and all sufficiently strong probability tails. -/
theorem induction_error_absorption {d : ℕ} (hd : 1 ≤ d) {η C : ℝ}
    (hη : 0 < η) (hC : 0 ≤ C) (D : ℕ) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁, ∀ p ≤ D, ∀ N : ℝ,
      Real.log L ^ (40 * d) ≤ N →
      2 * L ^ (-(η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ p))) +
        2 * Real.sqrt 2 * C * L ^ d * Real.exp (-N / 2) ≤ L ^ (-(η ^ 20)) := by
  obtain ⟨hgap, hsteps⟩ := induction_exponent_gap hη D
  obtain ⟨L₁, hL₁, hbound⟩ := eventually_absorb (θ := η ^ 20) hd hgap hC
  exact ⟨L₁, hL₁, fun L hL p hp N hN => hbound L hL _ N (hsteps p hp) hN⟩

/-- G10(a): the terminal probability exponent has the required asymptotic lower bound. -/
theorem eventually_final_exponent {d : ℕ} (hd : 1 ≤ d) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁,
      Real.log L ^ (40 * d) ≤ (⌊Real.log L ^ (40 * d)⌋₊ : ℝ) ^ (40 * d) := by
  obtain ⟨L₁, hL₁, hbound⟩ := eventually_log_pow_ge_four hd
  exact ⟨L₁, hL₁, fun L hL => log_pow_le_final_exponent hd (hbound L hL)⟩

/-- G10(a,c) with the source's actual terminal floor-power exponent substituted. -/
theorem induction_error_absorption_final {d : ℕ} (hd : 1 ≤ d) {η C : ℝ}
    (hη : 0 < η) (hC : 0 ≤ C) (D : ℕ) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁, ∀ p ≤ D,
      2 * L ^ (-(η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ p))) +
        2 * Real.sqrt 2 * C * L ^ d *
          Real.exp (-((⌊Real.log L ^ (40 * d)⌋₊ : ℝ) ^ (40 * d)) / 2) ≤
            L ^ (-(η ^ 20)) := by
  obtain ⟨A, hA, habsorb⟩ := induction_error_absorption hd hη hC D
  obtain ⟨B, _, hprob⟩ := eventually_final_exponent hd
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro L hL p hp
  exact habsorb L ((le_max_left _ _).trans hL) p hp _ (hprob L ((le_max_right _ _).trans hL))

end WaveTurbulence.MainGlue
