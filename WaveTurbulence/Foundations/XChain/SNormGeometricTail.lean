/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormSeries
public import Mathlib.Analysis.SpecificLimits.Normed
/-! A geometric spatial-norm bound yields the exact spatial bound on its Taylor tail. -/
public section
namespace WaveTurbulence.Induct
open scoped ENNReal

theorem contDiff_of_SNorm_bound {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℂ)
    (C : ℝ) (h : SNorm A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  classical
  have ht : SNorm A B f < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  unfold SNorm at ht
  split_ifs at ht with hf
  · exact hf.resolve_left hA
  · exact False.elim (not_lt_of_ge le_rfl ht)

theorem SNormR_geometric_tail_bound {d A B : ℕ} (hA : A ≠ 0)
    (f : ℕ → Mom d → ℝ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n, SNormR A B (f n) ≤ ENNReal.ofReal (C * r ^ n)) (M : ℕ) :
    SNormR A B (fun x => ∑' j, f (M + j) x) ≤ ENNReal.ofReal (C * r ^ M / (1 - r)) := by
  let g : ℕ → Mom d → ℂ := fun j x => (f (M + j) x : ℂ)
  let c : ℕ → ℝ := fun j => C * r ^ (M + j)
  have hc : ∀ j, 0 ≤ c j := fun j => mul_nonneg hC (pow_nonneg hr _)
  have hcs : Summable c := by
    have hs := (summable_geometric_of_lt_one hr hr1).mul_left (C * r ^ M)
    simpa only [c, pow_add, mul_assoc] using hs
  have hg : ∀ j, ContDiff ℝ A (g j) := fun j =>
    contDiff_of_SNorm_bound hA (g j) (c j) (h (M + j))
  have hs := SNorm_tsum_bound g c hc hcs hg (fun j => h (M + j))
  have he : (∑' j, c j) = C * r ^ M / (1 - r) := by
    simp only [c, pow_add, ← mul_assoc, tsum_mul_left, tsum_geometric_of_lt_one hr hr1, div_eq_mul_inv]
  rw [he] at hs
  have hfun : (fun x => ((∑' j, f (M + j) x : ℝ) : ℂ)) = fun x => ∑' j, g j x := by
    funext x
    exact Complex.ofReal_tsum _
  unfold SNormR
  rw [hfun]
  exact hs

end WaveTurbulence.Induct
