/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Fractional-power sums for exponent-pair smoothing

Explicit head and tail estimates for every frequency exponent `0 < kappa < 1`.
They generalize the square-root weights without a logarithmic loss, and are
pure numerical inputs to the conditional exponent-pair-to-circle transfer.
-/

public section

namespace WaveTurbulence.NumberTheory

open MeasureTheory intervalIntegral Set

/-- The first `H` values of `n^(kappa-1)` sum to at most `H^kappa/kappa`. -/
theorem sum_rpow_sub_one_le {kappa : ℝ} (hk : 0 < kappa) (hk1 : kappa ≤ 1) (H : ℕ) :
    (∑ i ∈ Finset.range H, ((i+1:ℕ):ℝ)^(kappa-1)) ≤ (H:ℝ)^kappa/kappa := by
  have ha : AntitoneOn (fun x : ℝ => x^(kappa-1)) (Ioc 0 (0+(H:ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith only [hk1])
  have hi : IntegrableOn (fun x : ℝ => x^(kappa-1)) (Icc 0 (0+(H:ℝ))) := by
    rw [zero_add]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg H)).mp
      (intervalIntegrable_rpow' (by linarith only [hk] : -1 < kappa-1))
  have hb := ha.sum_le_integral_of_integrableOn hi
  simp only [zero_add] at hb
  have he : (∫ x in (0:ℝ)..(H:ℝ), x^(kappa-1)) = (H:ℝ)^kappa/kappa := by
    rw [integral_rpow (Or.inl (by linarith only [hk] : -1 < kappa-1))]
    simp only [sub_add_cancel,Real.zero_rpow hk.ne',sub_zero]
  exact hb.trans_eq he

/-- The tail of `n^(kappa-2)` has the integral-test bound, uniformly in the
positive integer cutoff. -/
theorem tsum_rpow_sub_two_tail_le {kappa : ℝ} (hk1 : kappa < 1) {H : ℕ} (hH : 0 < H) :
    (∑' i : ℕ, ((i+H+1:ℕ):ℝ)^(kappa-2)) ≤ (H:ℝ)^(kappa-1)/(1-kappa) := by
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have ha : AntitoneOn (fun x : ℝ => x^(kappa-2)) (Ici (H:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hHR.trans_le hx) hxy (by linarith only [hk1])
  have hi : IntegrableOn (fun x : ℝ => x^(kappa-2)) (Ioi (H:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [hk1]) hHR
  have hb := AntitoneOn.tsum_comp_add_le_integral H ha hi (fun x hx => Real.rpow_nonneg (hHR.trans hx).le _)
  have he : (∫ x : ℝ in Ioi (H:ℝ), x^(kappa-2)) = (H:ℝ)^(kappa-1)/(1-kappa) := by
    rw [integral_Ioi_rpow_of_lt (by linarith only [hk1] : kappa-2 < -1) hHR]
    rw [show kappa-2+1 = kappa-1 by ring,show 1-kappa = -(kappa-1) by ring]
    simp only [div_neg,neg_div]
  exact hb.trans_eq he

/-- Summability of the fractional tail, used when comparing smoothing series. -/
theorem summable_rpow_sub_two_tail {kappa : ℝ} (hk1 : kappa < 1) (H : ℕ) :
    Summable (fun i : ℕ => ((i+H+1:ℕ):ℝ)^(kappa-2)) := by
  have hs := Real.summable_nat_rpow.mpr (by linarith only [hk1] : kappa-2 < -1)
  exact hs.comp_injective (fun i j h => by omega)

end WaveTurbulence.NumberTheory
