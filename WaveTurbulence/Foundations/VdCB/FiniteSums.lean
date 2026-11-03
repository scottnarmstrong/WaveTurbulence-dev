/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Sharp integer intervals and the trivial exponential-sum estimate

The interval is exactly `a<n≤b`, represented by integer floors. In
particular an integral endpoint contributes its full weight at the right
end and zero at the left end. This convention will be retained in the
truncated Poisson formula.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The finite set of integers in the sharp half-open real interval `(a,b]`. -/
@[expose] noncomputable def integerInterval (a b : ℝ) : Finset ℤ := Finset.Ioc ⌊a⌋ ⌊b⌋

theorem mem_integerInterval {a b : ℝ} {n : ℤ} :
    n ∈ integerInterval a b ↔ a < n ∧ (n : ℝ) ≤ b := by
  simp only [integerInterval, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- The actual sharp exponential sum. -/
@[expose] noncomputable def exponentialSum (f : ℝ → ℝ) (a b : ℝ) : ℂ :=
  ∑ n ∈ integerInterval a b, expPhase (f n)

theorem norm_exponentialSum_le_card (f : ℝ → ℝ) (a b : ℝ) :
    ‖exponentialSum f a b‖ ≤ (integerInterval a b).card := by
  unfold exponentialSum
  calc
    _ ≤ ∑ n ∈ integerInterval a b, ‖expPhase (f n)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_expPhase, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem card_integerInterval_le {a b : ℝ} (hab : a ≤ b) :
    ((integerInterval a b).card : ℝ) ≤ b - a + 1 := by
  have hfl : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono hab
  have hc : ((integerInterval a b).card : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by
    exact_mod_cast Int.card_Ioc_of_le ⌊a⌋ ⌊b⌋ hfl
  rw [hc]
  have ha := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  linarith only [ha, hb]

/-- The `(0,1)` estimate on every subinterval of `[N,2N]`, independent of
any phase regularity or derivative bounds. -/
theorem norm_exponentialSum_le_two_mul {N a b : ℝ} (hN : 1 ≤ N)
    (ha : N ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * N) (f : ℝ → ℝ) :
    ‖exponentialSum f a b‖ ≤ 2 * N := by
  exact (norm_exponentialSum_le_card f a b).trans
    ((card_integerInterval_le hab).trans (by linarith only [hN, ha, hb]))

end WaveTurbulence.VdCB
