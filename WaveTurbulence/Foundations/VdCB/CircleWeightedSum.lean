/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleCurvature
public import WaveTurbulence.Foundations.VdCB.AbelWeight
public import WaveTurbulence.Foundations.VdCB.Phase

/-!
# Removing the circle stationary weight by partial summation

This is an elementary transfer from a bound for actual initial dual
partial sums. It assumes no exponent-pair predicate or B-closure result.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- A bound for actual dual partial sums controls the weighted circle
sum with precisely the dyadic curvature-weight scale. -/
theorem norm_sum_circleDualWeight_mul_phase_le {R h Y : ℝ} (hh : 0 < h) (hY : 0 < Y)
    (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ m ≤ K,
      ‖∑ j ∈ Finset.range m, expPhase (circleLatticeDualPhase R h (Y + j))‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, (circleDualWeight R h (Y + j) : ℂ) *
      expPhase (circleLatticeDualPhase R h (Y + j))‖ ≤
        (Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ)) * B := by
  let w : ℕ → ℝ := fun j => circleDualWeight R h (Y + j)
  let z : ℕ → ℂ := fun j => expPhase (circleLatticeDualPhase R h (Y + j))
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp only [w, circleDualWeight]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg R) hh.le) (Real.rpow_nonneg (by positivity) _)
  have hw : Antitone w := by
    intro i j hij
    change circleDualWeight R h (Y + j) ≤ circleDualWeight R h (Y + i)
    exact (antitoneOn_circleDualWeight (R := R) hh)
      (show Y + (i : ℝ) ∈ Set.Ici 0 from add_nonneg hY.le (Nat.cast_nonneg i))
      (show Y + (j : ℝ) ∈ Set.Ici 0 from add_nonneg hY.le (Nat.cast_nonneg j))
      (add_le_add le_rfl (show (i : ℝ) ≤ j by exact_mod_cast hij))
  have hhbound := norm_sum_range_antitone_smul_le w z hw0 hw K hB hpartial
  have hweight := circleDualWeight_le (R := R) hh hY (le_refl Y)
  have hscale := mul_le_mul_of_nonneg_right hweight hB
  have hbound := hhbound.trans (by simpa only [w, Nat.cast_zero, add_zero] using hscale)
  simpa only [w, z, Complex.real_smul] using hbound

end WaveTurbulence.VdCB
