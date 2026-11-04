/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceMixedCorePower
public import WaveTurbulence.Foundations.Sumint.StrictPowerAbsorption

/-!
# A fixed polynomial lattice cost for the actual selected-time trace

The eight-input counting cost is at most a step-dependent constant times
L to 8d. Enlarging the lattice threshold absorbs that constant into one
additional d-power. This does not affect the exponential-in-M constant.
-/

public section
open ENNReal
namespace WaveTurbulence.Sumint

/-- The literal counting cost grows at most like L to 8d with an explicit step-dependent coefficient. -/
theorem sourceTraceCountingCost_le {d N : ℕ} {L η : ℝ} (hL : 1 ≤ L) :
    sourceTraceCountingCost d N L η ≤
      ENNReal.ofReal ((3*max 1 (((N:ℝ)+2)^(1-3*η)))^8*9^(8*d)*L^((8*d:ℕ):ℝ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ 3*max 1 (((N:ℝ)+2)^(1-3*η)) := by positivity
  unfold sourceTraceCountingCost
  rw [← ENNReal.ofReal_pow (mul_nonneg hK (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  have hq : 8*L+1 ≤ 9*L := by linarith only [hL]
  calc
    _ ≤ (3*max 1 (((N:ℝ)+2)^(1-3*η))*(9*L)^d)^8 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _) hK) _
    _ = _ := by
      rw [mul_pow,mul_pow,← pow_mul,Real.rpow_natCast,mul_pow,Nat.mul_comm d 8]
      ring

/-- The source trace counting cost is at most L to 9d once the step-dependent threshold is enlarged. -/
theorem exists_sourceTraceCountingCost_le_power (d N : ℕ) (hd : 0 < d) (η : ℝ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      sourceTraceCountingCost d N L η ≤ ENNReal.ofReal (L^(9*(d:ℝ))) := by
  have he : ((8*d:ℕ):ℝ) < 9*(d:ℝ) := by
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    push_cast
    linarith only [hd']
  obtain ⟨R,hR,hbound⟩ := exists_coefficient_power_le
    ((3*max 1 (((N:ℝ)+2)^(1-3*η)))^8*9^(8*d)) ((8*d:ℕ):ℝ) (9*(d:ℝ)) he
  refine ⟨R,hR,?_⟩
  intro L hL
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  exact (sourceTraceCountingCost_le (N := N) (η := η) hL1).trans
    (ENNReal.ofReal_le_ofReal (hbound L hL))

end WaveTurbulence.Sumint
