/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Torus.Inversion
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Local normal convergence of Schwartz periodizations

Schwartz decay gives a summable bound for integer translates, uniformly
on every compact subset. This provides the convergence input for
multidimensional Poisson summation in TARGET L1035, L1541, L1575.
-/

public section

open TopologicalSpace
open scoped SchwartzMap

namespace WaveTurbulence.Fourier

/-- The polynomial Schwartz bound with a constant expressed by two seminorms. -/
theorem schwartz_polynomial_weight_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (N : ℕ) (f : 𝓢(V, ℂ)) (x : V) :
    (1 + ‖x‖) ^ N * ‖f x‖ ≤ (2 : ℝ) ^ (N - 1) *
      (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ N 0 f) := by
  have h0 := SchwartzMap.norm_le_seminorm ℂ f x
  have hN := SchwartzMap.norm_pow_mul_le_seminorm ℂ f N x
  calc
    _ ≤ (2 : ℝ) ^ (N - 1) * ((1 + ‖x‖ ^ N) * ‖f x‖) := by
      simpa only [one_pow, mul_assoc] using mul_le_mul_of_nonneg_right
        (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg x) N) (norm_nonneg (f x))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [h0, hN]

/-- The coordinatewise integer inclusion preserves the sup norm. -/
theorem norm_integerCast {d : ℕ} (n : Fin d → ℤ) :
    ‖(fun i => (n i : ℝ))‖ = ‖n‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg n)).mpr
    intro i
    simpa only [Int.norm_eq_abs, Real.norm_eq_abs] using norm_le_pi_norm n i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (n i : ℝ)))).mpr
    intro i
    simpa only [Int.norm_eq_abs, Real.norm_eq_abs] using norm_le_pi_norm (fun i => (n i : ℝ)) i

/-- A uniform polynomial bound for translated Schwartz samples on a ball. -/
theorem schwartz_translate_weight_le {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ))
    (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {x : Fin d → ℝ} (hx : ‖x‖ ≤ R)
    (n : Fin d → ℤ) :
    (1 + ‖n‖) ^ N * ‖f (x + fun i => (n i : ℝ))‖ ≤
      ((2 : ℝ) ^ (N - 1) *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ N 0 f)) * (1 + R) ^ N := by
  let y := x + fun i => (n i : ℝ)
  have hn : ‖n‖ ≤ ‖y‖ + ‖x‖ := by
    rw [← norm_integerCast n]
    simpa [y] using norm_sub_le y x
  have hbase : 1 + ‖n‖ ≤ (1 + R) * (1 + ‖y‖) := by
    nlinarith [norm_nonneg y]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖n‖) hbase N
  rw [mul_pow] at hp
  calc
    _ ≤ ((1 + R) ^ N * (1 + ‖y‖) ^ N) * ‖f y‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ((1 + ‖y‖) ^ N * ‖f y‖) * (1 + R) ^ N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (schwartz_polynomial_weight_le N f y) (by positivity)

/-- Integer translates of a Schwartz function converge normally on each compact set. -/
theorem schwartz_translates_locally_summable {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ))
    (K : Compacts (Fin d → ℝ)) :
    Summable fun n : Fin d → ℤ =>
      ‖((f.toContinuousMap).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  let R' := max 0 R
  have hR' : 0 ≤ R' := le_max_left _ _
  let C := ((2 : ℝ) ^ (2 * d - 1) *
    (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ (2 * d) 0 f)) * (1 + R') ^ (2 * d)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by positivity)
      (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))) (by positivity)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (WaveTurbulence.summable_one_add_norm_zpow.mul_left C)
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (by positivity))).mpr
  intro x
  have hx : ‖(x : Fin d → ℝ)‖ ≤ R' := by
    have hh := hR x.property
    simp only [Metric.mem_closedBall, dist_zero_right] at hh
    exact hh.trans (le_max_right _ _)
  have hb := schwartz_translate_weight_le f (2 * d) hR' hx n
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖n‖) _)).mpr
  change ‖f ((x : Fin d → ℝ) + fun i => (n i : ℝ))‖ * (1 + ‖n‖) ^ (2 * d) ≤ C
  simpa only [C, mul_comm] using hb

end WaveTurbulence.Fourier
