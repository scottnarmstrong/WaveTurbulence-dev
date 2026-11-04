/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OneClockCouple
public import WaveTurbulence.Foundations.Incoh.FiniteLayerCutoff

/-! # Actual passive-clock shifts on upper external unit boxes -/

public section
noncomputable section
namespace WaveTurbulence.Incoh

/-- The passive shift places the auxiliary clock above its complete layer while leaving the
actual active clock unchanged. -/
theorem RootCoordinates.oneClockShift_upper_bounds {d n : ℕ} (R : RootCoordinates n)
    (Q : Fin n → LayerLink d) (a : Fin 2) (b : ℝ) (t : Fin 2 → ℝ)
    (ha : R.baseRootTimes Q a ≤ t a) (hp : ∀ j, j ≠ a → b ≤ t j) :
    (R.baseRootTimes Q ≤ t + R.oneClockShift a Q b) ∧
      (∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j) := by
  constructor
  · intro j
    by_cases hj : j = a
    · subst j
      simpa only [Pi.add_apply, oneClockShift, ite_true, add_zero] using ha
    · have h := hp j hj
      simp only [Pi.add_apply, oneClockShift, hj, ite_false]
      linarith only [h]
  · intro j hj
    have h := hp j hj
    simp only [Pi.add_apply, oneClockShift, hj, ite_false]
    linarith only [h]

/-- The chosen finite-layer cutoff covers both the actual active primitive and the complete
auxiliary passive layer, uniformly in the passive external base. -/
theorem RootCoordinates.finiteLayerCutoff_one_on_oneClock_rectangle {d n : ℕ} (R : RootCoordinates n)
    (Q : Fin n → LayerLink d) (a : Fin 2) (b : ℝ) (D : ℕ) (t : Fin 2 → ℝ)
    (hbase : 0 ≤ R.baseRootTimes Q a) (ha : t a ≤ (D : ℝ) + 1)
    (hp : ∀ j, j ≠ a → t j ≤ b + 1) :
    ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), finiteLayerCutoff D s = 1 := by
  intro j s hs
  apply finiteLayerCutoff_eq_one
  rw [abs_of_nonneg hs.1]
  have hs' := hs.2
  by_cases hj : j = a
  · subst j
    simp only [Pi.add_apply, Pi.sub_apply, oneClockShift, ite_true, add_zero] at hs'
    linarith only [hs', ha, hbase]
  · have h := hp j hj
    simp only [Pi.add_apply, Pi.sub_apply, oneClockShift, hj, ite_false] at hs'
    have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    linarith only [hs', h, hD]

end WaveTurbulence.Incoh
