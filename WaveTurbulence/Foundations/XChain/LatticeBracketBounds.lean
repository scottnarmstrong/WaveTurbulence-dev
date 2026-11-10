/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.JbrBounds
public import WaveTurbulence.Foundations.NLS.AkClass
public import WaveTurbulence.Foundations.NLS.FourierEquation
/-! Peetre and absolute lattice-weight estimates, reusing the fixedpoint scratch proofs. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
variable {d : ℕ}
theorem jbr_pos'' (x : Mom d) : 0 < jbr x := Real.sqrt_pos.2 (by positivity)

theorem jbr_sq (x : Mom d) : jbr x ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)

/-- Peetre: `⟨x + y⟩ ≤ √2 ⟨x⟩ ⟨y⟩`. -/
theorem jbr_add_le (x y : Mom d) : jbr (x + y) ≤ Real.sqrt 2 * jbr x * jbr y := by
  have h1 : jbr (x + y) ^ 2 ≤ (Real.sqrt 2 * jbr x * jbr y) ^ 2 := by
    rw [jbr_sq, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), jbr_sq, jbr_sq]
    have := norm_add_le x y
    have hx := norm_nonneg x
    have hy := norm_nonneg y
    have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]
  have h0 : 0 ≤ Real.sqrt 2 * jbr x * jbr y :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (jbr_pos'' x).le) (jbr_pos'' y).le
  exact (pow_le_pow_iff_left₀ (jbr_pos'' _).le h0 two_ne_zero).1 h1

theorem jbr_neg (x : Mom d) : jbr (-x) = jbr x := by simp [jbr]

theorem jbr_units_smul (ζ : ℤˣ) (x : Mom d) : jbr ((ζ : ℤ) • x) = jbr x := by
  rcases Int.units_eq_one_or ζ with h | h <;> simp [h, jbr_neg]

/-! ## Lattice sums -/

theorem one_add_norm_le_jbr {L : ℝ} (hL : 1 ≤ L) (n : Fin d → ℤ) :
    1 + ‖n‖ ≤ Real.sqrt 2 * L * jbr (latticePoint L n) := by
  have hLpos : 0 < L := by linarith
  have hcoord : ‖n‖ / L ≤ ‖latticePoint L n‖ := by
    rw [div_le_iff₀ hLpos]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have h2 : |(n j : ℝ) / L| ^ 2 ≤ ‖latticePoint L n‖ ^ 2 := by
      rw [sq_abs, NLS.norm_latticePoint_sq]
      exact Finset.single_le_sum (f := fun j => ((n j : ℝ) / L) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h3 : |(n j : ℝ) / L| ≤ ‖latticePoint L n‖ :=
      (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
    rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos] at h3
    rw [Int.norm_eq_abs]
    exact h3
  have hj : 1 + ‖latticePoint L n‖ ≤ Real.sqrt 2 * jbr (latticePoint L n) := by
    have h1 : (1 + ‖latticePoint L n‖) ^ 2 ≤ (Real.sqrt 2 * jbr (latticePoint L n)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), jbr_sq]
      nlinarith [sq_nonneg (‖latticePoint L n‖ - 1)]
    exact (pow_le_pow_iff_left₀ (by positivity)
      (mul_nonneg (Real.sqrt_nonneg 2) (jbr_pos'' _).le) two_ne_zero).1 h1
  calc 1 + ‖n‖ ≤ L * (1 + ‖latticePoint L n‖) := by
        have := mul_le_mul_of_nonneg_left hcoord hLpos.le
        rw [mul_div_cancel₀ _ hLpos.ne'] at this
        nlinarith
    _ ≤ L * (Real.sqrt 2 * jbr (latticePoint L n)) := mul_le_mul_of_nonneg_left hj hLpos.le
    _ = Real.sqrt 2 * L * jbr (latticePoint L n) := by ring

/-- `⟨m/L⟩^{−(d+1)} ≤ (√2 L)^{d+1} (1 + |m|)^{−(d+1)}`. -/
theorem jbr_rpow_neg_le {L : ℝ} (hL : 1 ≤ L) (m : Fin d → ℤ) :
    jbr (latticePoint L m) ^ (-((d : ℝ) + 1)) ≤ (Real.sqrt 2 * L) ^ (d + 1) * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
  have hj := jbr_pos'' (latticePoint L m)
  have h1 := one_add_norm_le_jbr hL m
  have hpos : 0 < 1 + ‖m‖ := by positivity
  have hs2L : 0 < Real.sqrt 2 * L := mul_pos (by positivity) (by linarith)
  rw [Real.rpow_neg hj.le, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  calc (jbr (latticePoint L m) ^ (d + 1))⁻¹
      = (Real.sqrt 2 * L) ^ (d + 1) * ((Real.sqrt 2 * L * jbr (latticePoint L m)) ^ (d + 1))⁻¹ := by
        rw [mul_pow (Real.sqrt 2 * L), mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs2L.ne'), one_mul]
    _ ≤ (Real.sqrt 2 * L) ^ (d + 1) * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
        gcongr

theorem summable_jbr_rpow_neg {L : ℝ} (hL : 1 ≤ L) :
    Summable fun m : Fin d → ℤ => jbr (latticePoint L m) ^ (-((d : ℝ) + 1)) :=
  Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (jbr_pos'' _).le _) (jbr_rpow_neg_le hL)
    (NLS.summable_inv_one_add_norm_pow.mul_left _)

/-- The lattice sum `S = ∑_m ⟨m/L⟩^{−(d+1)}`. -/
noncomputable def latSum (d : ℕ) (L : ℝ) : ℝ := ∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-((d : ℝ) + 1))

theorem latSum_le {L : ℝ} (hL : 1 ≤ L) :
    latSum d L ≤ (Real.sqrt 2 * L) ^ (d + 1) * ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
  rw [← tsum_mul_left]
  exact (summable_jbr_rpow_neg hL).tsum_le_tsum (jbr_rpow_neg_le hL)
    (NLS.summable_inv_one_add_norm_pow.mul_left _)


end WaveTurbulence.Induct
