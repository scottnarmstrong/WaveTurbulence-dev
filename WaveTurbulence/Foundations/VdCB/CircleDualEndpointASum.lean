/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleBScaling

/-!
# A single endpoint frequency in the weighted dual estimate

A closed endpoint can add one frequency to the A-process window. Its
actual stationary weight is controlled directly by the same B-scale.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The transformed circle dual scale remains valid with one final
endpoint frequency beyond the pure A-process block length. -/
theorem norm_sum_circleDualWeight_mul_le_B_scale_succ (a : ℤ) (K : ℕ) (p q : ℝ)
    {R h U : ℝ} (hR : 0 < R) (hh : 0 < h) (hU : 0 < U)
    (hY : 1 ≤ (a : ℝ) + 1) (hhY : h ≤ (a : ℝ) + 1)
    (hRY : ((a : ℝ) + 1) ^ 2 ≤ R * h ^ 2) (hK : (K : ℝ) ≤ 2 * ((a : ℝ) + 1) + 1)
    (hfrequency : R * h ^ 2 / (9 * U) ≤ ((a : ℝ) + 1) ^ 2) :
    ‖∑ j ∈ Finset.range K, (circleDualWeight R h ((a : ℝ) + 1 + j) : ℂ) *
      expPhase (circleLatticeDualPhase R h ((a : ℝ) + 1 + j) + p * ((a : ℝ) + 1 + j) + q)‖ ≤
      154618822665 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  let P := h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  by_cases hshort : (K : ℝ) ≤ 2 * ((a : ℝ) + 1)
  · exact (norm_sum_circleDualWeight_mul_le_B_scale a K p q hR hh hU hY hhY hRY hshort hfrequency).trans
      (by change 154618822656 * P ≤ 154618822665 * P; nlinarith only [hP])
  have hKpos : 1 ≤ K := by
    by_contra h
    have hzero : K = 0 := by omega
    simp only [hzero, Nat.cast_zero] at hshort
    linarith only [hshort, hY]
  have hKprev : ((K - 1 : ℕ) : ℝ) ≤ 2 * ((a : ℝ) + 1) := by
    have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by exact_mod_cast Nat.sub_add_cancel hKpos
    have heq : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by linarith only [hcast]
    linarith only [heq, hK]
  let Z : ℕ → ℂ := fun j => (circleDualWeight R h ((a : ℝ) + 1 + j) : ℂ) *
    expPhase (circleLatticeDualPhase R h ((a : ℝ) + 1 + j) + p * ((a : ℝ) + 1 + j) + q)
  have hmain : ‖∑ j ∈ Finset.range (K - 1), Z j‖ ≤ 154618822656 * P :=
    norm_sum_circleDualWeight_mul_le_B_scale a (K - 1) p q hR hh hU hY hhY hRY hKprev hfrequency
  have hlast : ‖Z (K - 1)‖ ≤ 9 * P := by
    dsimp only [Z]
    have hnon : 0 ≤ circleDualWeight R h ((a : ℝ) + 1 + (K - 1 : ℕ)) := by
      unfold circleDualWeight
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    rw [norm_mul, norm_expPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon]
    apply LE.le.trans _ (circleDualWeight_le_B_scale hR hh hU hY hRY hfrequency)
    apply antitoneOn_circleDualWeight hh
    · exact show (a : ℝ) + 1 ∈ Set.Ici 0 from (zero_le_one.trans hY)
    · exact show (a : ℝ) + 1 + (K - 1 : ℕ) ∈ Set.Ici 0 from
        add_nonneg (zero_le_one.trans hY) (Nat.cast_nonneg _)
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsplit : (∑ j ∈ Finset.range K, Z j) = (∑ j ∈ Finset.range (K - 1), Z j) + Z (K - 1) := by
    simpa only [Nat.sub_add_cancel hKpos] using Finset.sum_range_succ Z (K - 1)
  change ‖∑ j ∈ Finset.range K, Z j‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hmain hlast).trans_eq (by ring))

end WaveTurbulence.VdCB
