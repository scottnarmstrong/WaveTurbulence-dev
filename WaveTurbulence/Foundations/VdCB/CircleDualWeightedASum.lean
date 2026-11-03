/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualASum
public import WaveTurbulence.Foundations.VdCB.CircleWeight
public import WaveTurbulence.Foundations.VdCB.AbelWeight
public import WaveTurbulence.Foundations.VdCB.IntegerRangeSum

/-!
# The weighted actual circle dual A-process estimate

Every initial dual partial sum satisfies the proved fifth-derivative
A-scale. Partial summation removes the actual decreasing curvature weight.
No exponential-sum estimate or derivative formula is assumed here.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Weighted corrected circle dual estimate on an actual integer block.
The real linear phase is arbitrary, including all lattice translations. -/
theorem norm_sum_circleDualWeight_mul_add_linear_le (a : ℤ) (K : ℕ) (p q : ℝ)
    {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hY : 1 ≤ (a : ℝ) + 1) (hhY : h ≤ (a : ℝ) + 1)
    (hRY : ((a : ℝ) + 1) ^ 2 ≤ R * h ^ 2) (hK : (K : ℝ) ≤ 2 * ((a : ℝ) + 1)) :
    ‖∑ j ∈ Finset.range K, (circleDualWeight R h ((a : ℝ) + 1 + j) : ℂ) *
      expPhase (circleLatticeDualPhase R h ((a : ℝ) + 1 + j) + p * ((a : ℝ) + 1 + j) + q)‖ ≤
      17179869184 * Real.sqrt R * h * (R * h ^ 2 / ((a : ℝ) + 1) ^ 2) ^ ((1 : ℝ) / 30) *
        ((a : ℝ) + 1) ^ (-(19 / 30) : ℝ) := by
  let Y : ℝ := (a : ℝ) + 1
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  let w : ℕ → ℝ := fun j => circleDualWeight R h (Y + j)
  let z : ℕ → ℂ := fun j => expPhase (circleLatticeDualPhase R h (Y + j) + p * (Y + j) + q)
  let B : ℝ := 17179869184 * ((R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ ((26 : ℝ) / 30))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpartial (m : ℕ) (hm : m ≤ K) : ‖∑ j ∈ Finset.range m, z j‖ ≤ B := by
    have hmR : (m : ℝ) ≤ 2 * Y := (by exact_mod_cast hm : (m : ℝ) ≤ K).trans hK
    have he := norm_sum_circleLatticeDualPhase_add_linear_le a m p q hR hh hY hhY hRY le_rfl
      (by dsimp only [Y] at hmR; linarith only [hmR, hY]) (by linarith only [hmR, hYp])
    rw [sum_Ioc_int_eq_range] at he
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [z, Y]
    push_cast
    rw [show (a : ℝ) + 1 + (j : ℝ) = (a : ℝ) + j + 1 by ring]
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp only [w, circleDualWeight]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg R) hh.le) (Real.rpow_nonneg (by positivity) _)
  have hw : Antitone w := by
    intro i j hij
    change circleDualWeight R h (Y + j) ≤ circleDualWeight R h (Y + i)
    exact (antitoneOn_circleDualWeight (R := R) hh)
      (show Y + (i : ℝ) ∈ Set.Ici 0 from add_nonneg hYp.le (Nat.cast_nonneg i))
      (show Y + (j : ℝ) ∈ Set.Ici 0 from add_nonneg hYp.le (Nat.cast_nonneg j))
      (add_le_add le_rfl (show (i : ℝ) ≤ j by exact_mod_cast hij))
  have he := norm_sum_range_antitone_smul_le w z hw0 hw K hB hpartial
  have hweight := mul_le_mul_of_nonneg_right (circleDualWeight_le (R := R) hh hYp (le_refl Y)) hB
  have hbound := he.trans (by simpa only [w, Nat.cast_zero, add_zero] using hweight)
  have hscale : (Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ)) * B =
      17179869184 * Real.sqrt R * h * (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ (-(19 / 30) : ℝ) := by
    dsimp only [B]
    calc
      _ = (17179869184 * Real.sqrt R * h * (R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30)) *
          (Y ^ (-(3 / 2) : ℝ) * Y ^ ((26 : ℝ) / 30)) := by ring
      _ = _ := by rw [← Real.rpow_add hYp]; norm_num
  rw [hscale] at hbound
  simpa only [w, z, Y, Complex.real_smul] using hbound

end WaveTurbulence.VdCB
