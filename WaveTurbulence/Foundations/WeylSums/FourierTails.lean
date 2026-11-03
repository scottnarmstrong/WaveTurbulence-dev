/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactFourier
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compact Fourier replacements with explicit tails

A Fourier weight is never silently replaced by a compactly supported one.
Truncation leaves a remainder bounded by its `L¹` tail times the uniform
bound for the one-dimensional factors. Those tails tend to zero. This makes
the compact replacement in TARGET after (lemcub4) an honest approximation.
-/

public section
open MeasureTheory Filter
open scoped Topology SchwartzMap
namespace WaveTurbulence.WeylSums

/-- A compactly supported replacement of an integrable Fourier weight. -/
@[expose] noncomputable def compactFourierWeight {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (R : ℝ) :=
  (Metric.closedBall 0 R).indicator F

theorem compactFourierWeight_hasCompactSupport {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (R : ℝ) :
    HasCompactSupport (compactFourierWeight F R) := by
  apply HasCompactSupport.intro (isCompact_closedBall 0 R)
  intro x hx
  exact Set.indicator_of_notMem hx _

theorem integrable_compactFourierWeight {m : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → ℂ} (hF : Integrable F) (R : ℝ) :
    Integrable (compactFourierWeight F R) :=
  hF.indicator measurableSet_closedBall

/-- The error from compact replacement, for any bounded measurable kernel.
For the tensor reduction, `M` is the product of the one-dimensional bounds. -/
theorem norm_fourier_truncation_error_le {m : ℕ}
    {F K : EuclideanSpace ℝ (Fin m) → ℂ} (hF : Integrable F)
    (hK : AEStronglyMeasurable K volume) (M R : ℝ)
    (hb : ∀ x, ‖K x‖ ≤ M) :
    ‖(∫ x, F x * K x) - (∫ x, compactFourierWeight F R x * K x)‖ ≤
      (∫ x in (Metric.closedBall 0 R)ᶜ, ‖F x‖) * M := by
  have hFK : Integrable (fun x => F x * K x) :=
    hF.mul_bdd hK (Eventually.of_forall hb)
  have heq : (∫ x, compactFourierWeight F R x * K x) =
      ∫ x in Metric.closedBall 0 R, F x * K x := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [compactFourierWeight, Set.indicator_mul_left]
  rw [heq, ← integral_add_compl measurableSet_closedBall hFK, add_sub_cancel_left]
  have hh : ‖∫ x in (Metric.closedBall 0 R)ᶜ, F x * K x‖ ≤
      ∫ x in (Metric.closedBall 0 R)ᶜ, ‖F x‖ * M := by
    apply norm_integral_le_of_norm_le (hF.norm.mul_const M).restrict
    exact Eventually.of_forall (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))
  simpa only [integral_mul_const] using hh

/-- The `L¹` tail of every integrable Fourier weight vanishes. -/
theorem tendsto_fourier_tail_zero {m : ℕ}
    {F : EuclideanSpace ℝ (Fin m) → ℂ} (hF : Integrable F) :
    Tendsto (fun n : ℕ => ∫ x in {x : EuclideanSpace ℝ (Fin m) | (n : ℝ) < ‖x‖}, ‖F x‖)
      atTop (𝓝 0) := by
  have hi : (⋂ n : ℕ, {x : EuclideanSpace ℝ (Fin m) | (n : ℝ) < ‖x‖}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact (not_lt_of_ge hn.le) (hx n)
  have hh := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x : EuclideanSpace ℝ (Fin m) => ‖F x‖)
    (fun n : ℕ => measurableSet_lt measurable_const continuous_norm.measurable)
    (show Antitone (fun n : ℕ => {x : EuclideanSpace ℝ (Fin m) | (n : ℝ) < ‖x‖}) from
      fun i j hij x hx => (show (i : ℝ) < ‖x‖ from lt_of_le_of_lt (Nat.cast_le.mpr hij) hx))
    (show ∃ n : ℕ, IntegrableOn (fun x => ‖F x‖) {x | (n : ℝ) < ‖x‖} volume from ⟨0, hF.norm.restrict⟩)
  simpa [hi] using hh

/-- A Schwartz weight, including the Fourier transform of a smooth compact
cutoff, admits compact replacements with arbitrary polynomial pointwise error.
This bound also applies at lattice sampling points. -/
theorem exists_schwartz_compact_error_bound {m : ℕ}
    (F : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (P : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ x,
      ‖F x - compactFourierWeight F R x‖ ≤ A / R^P := by
  let A : ℝ := (SchwartzMap.seminorm ℝ P 0) F
  have hb (x : EuclideanSpace ℝ (Fin m)) : ‖x‖^P * ‖F x‖ ≤ A :=
    SchwartzMap.norm_pow_mul_le_seminorm ℝ F P x
  have hA : 0 ≤ A := (by positivity : 0 ≤ ‖(0 : EuclideanSpace ℝ (Fin m))‖^P * ‖F 0‖).trans (hb 0)
  refine ⟨A, hA, ?_⟩
  intro R hR x
  have hRp : 0 < R := by linarith
  by_cases hx : x ∈ Metric.closedBall 0 R
  · simp only [compactFourierWeight, Set.indicator_of_mem hx, sub_self, norm_zero]
    exact div_nonneg hA (pow_nonneg hRp.le _)
  · simp only [compactFourierWeight, Set.indicator_of_notMem hx, sub_zero]
    have hxR : R ≤ ‖x‖ := by
      have hh : ¬ ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact (lt_of_not_ge hh).le
    apply (le_div_iff₀ (pow_pos hRp P)).mpr
    have hpw : R^P ≤ ‖x‖^P := pow_le_pow_left₀ hRp.le hxR P
    have hm : ‖F x‖ * R^P ≤ ‖x‖^P * ‖F x‖ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpw (norm_nonneg (F x))
    exact hm.trans (hb x)

end WaveTurbulence.WeylSums
