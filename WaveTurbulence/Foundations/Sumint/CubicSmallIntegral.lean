/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicWeylBridge
public import WaveTurbulence.Foundations.Sumint.CubicTimeKernel
public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise
import Mathlib.Tactic

/-!
# Integrating the cubic small-time square

The literal source cubic sum has an integrable two-time majorant in
all dimensions `d≥3`, uniformly in both quadratic forms and all centers.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- A closed square in absolute-value coordinates is a product order interval. -/
theorem square_window_eq_Icc (B : ℝ) :
    {st : ℝ × ℝ | |st.1| ≤ B ∧ |st.2| ≤ B} = Icc (-B,-B) (B,B) := by
  ext st
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Prod.le_def, abs_le]
  tauto

/-- Uniform integrated estimate for both source cubic sums on the small-time square. -/
theorem exists_cubic_small_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (sel : Bool) (a b c ξ ζ ω : Mom d),
      (∫ st : ℝ × ℝ in {st | |st.1| ≤ L ∧ |st.2| ≤ L},
        ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖) ≤ C * L^(3*d) := by
  obtain ⟨C, hC, hb⟩ := exists_cubic_weyl_small_bound d
  let k := fun st : ℝ × ℝ => 1 / (1+|st.1|+|st.2|)^d
  have hk : Integrable k := integrable_cubicTimeKernel_nat hd
  have hkn (st : ℝ × ℝ) : 0 ≤ k st := by dsimp [k]; positivity
  refine ⟨C * ∫ st, k st, mul_nonneg hC (integral_nonneg hkn), ?_⟩
  intro L hL sel a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  let S := {st : ℝ × ℝ | |st.1| ≤ L ∧ |st.2| ≤ L}
  have hS : MeasurableSet S := by rw [show S = Icc (-L,-L) (L,L) from square_window_eq_Icc L]; exact measurableSet_Icc
  have hiS : IntegrableOn (fun st : ℝ × ℝ =>
      ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖) S := by
    rw [show S = Icc (-L,-L) (L,L) from square_window_eq_Icc L]
    exact (WeylSums.continuous_cubicLatticeSum hLp sel a b c ξ ζ ω).norm.integrableOn_Icc
  have hmajor (st : ℝ × ℝ) (hs : st ∈ S) :
      ‖WeylSums.cubicLatticeSum L st.1 st.2 sel a b c ξ ζ ω‖ ≤ (C * L^(3*d)) * k st := by
    simpa only [k, mul_one_div, add_assoc, add_comm |st.1|, add_left_comm] using
      hb hL st.2 st.1 hs.2 hs.1 sel a b c ξ ζ ω
  calc
    _ ≤ ∫ st in S, (C * L^(3*d)) * k st :=
      setIntegral_mono_on hiS (hk.const_mul _).integrableOn hS hmajor
    _ ≤ ∫ st : ℝ × ℝ, (C * L^(3*d)) * k st :=
      setIntegral_le_integral (hk.const_mul _) (ae_of_all _ (fun st =>
        mul_nonneg (mul_nonneg hC (pow_nonneg hLp.le _)) (hkn st)))
    _ = _ := by rw [integral_const_mul]; ring

end WaveTurbulence.Sumint
