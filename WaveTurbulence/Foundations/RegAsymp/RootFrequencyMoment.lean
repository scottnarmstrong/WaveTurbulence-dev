/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FrequencyProductMoment
public import WaveTurbulence.Frozen.Defs.Mom

/-! # Paying root derivatives and the NT modulation loss with fixed leaf moments -/

public section
namespace WaveTurbulence.RegAsymp

/-- J root derivatives and the one NT frequency moment use order J+1 at
each individual leaf, independently of the number of leaves. -/
theorem root_frequency_moment_mul_le_product {ι : Type} [Fintype ι] {d : ℕ}
    (v : ι → Mom d) (J : ℕ) :
    (1+‖∑ i, v i‖)^J*(1+∑ i, ‖v i‖) ≤ ∏ i, (1+‖v i‖)^(J+1) := by
  have hn : ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have ha : 1+‖∑ i, v i‖ ≤ 1+∑ i, ‖v i‖ := by linarith only [hn]
  have hp := one_add_sum_le_prod_one_add Finset.univ (fun i => ‖v i‖)
    (fun i _ => norm_nonneg (v i))
  calc
    _ ≤ (1+∑ i, ‖v i‖)^J*(1+∑ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ha J)
        (by positivity)
    _ = (1+∑ i, ‖v i‖)^(J+1) := (pow_succ _ _).symm
    _ ≤ (∏ i, (1+‖v i‖))^(J+1) := pow_le_pow_left₀ (by positivity) hp _
    _ = _ := by rw [Finset.prod_pow]

end WaveTurbulence.RegAsymp
