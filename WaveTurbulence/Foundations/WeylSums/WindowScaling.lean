/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ArcProfile
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Exact time rescaling on two-sided minor-arc windows -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The change `s=c*t` on a two-sided time window, including its Jacobian. -/
theorem integral_abs_window_div (f : ℝ → ℝ) (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in {s : ℝ | a ≤ |s| ∧ |s| ≤ b}, f (s/c)) =
      c * ∫ t : ℝ in {t : ℝ | a/c ≤ |t| ∧ |t| ≤ b/c}, f t := by
  let S : Set ℝ := {s : ℝ | a ≤ |s| ∧ |s| ≤ b}
  let T : Set ℝ := {t : ℝ | a/c ≤ |t| ∧ |t| ≤ b/c}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hmem (s : ℝ) : s/c ∈ T ↔ s ∈ S := by
    simp only [T, S, Set.mem_ofPred_eq, abs_div, abs_of_pos hc, div_le_div_iff_of_pos_right hc]
  have heq (s : ℝ) : S.indicator (fun s => f (s/c)) s = T.indicator f (c⁻¹*s) := by
    rw [show c⁻¹*s = s/c by ring]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem s).mpr hs)]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun ht => hs ((hmem s).mp ht))]
  change (∫ s in S, f (s/c)) = c * ∫ t in T, f t
  rw [← integral_indicator hS, ← integral_indicator hT]
  simp_rw [heq]
  rw [Measure.integral_comp_mul_left]
  simp only [inv_inv, abs_of_pos hc, smul_eq_mul]

/-- Integrability is preserved by the same exact window rescaling. -/
theorem integrableOn_abs_window_div {f : ℝ → ℝ} (a b : ℝ) {c : ℝ} (hc : 0 < c)
    (hi : IntegrableOn f {t : ℝ | a/c ≤ |t| ∧ |t| ≤ b/c}) :
    IntegrableOn (fun s => f (s/c)) {s : ℝ | a ≤ |s| ∧ |s| ≤ b} := by
  let S : Set ℝ := {s : ℝ | a ≤ |s| ∧ |s| ≤ b}
  let T : Set ℝ := {t : ℝ | a/c ≤ |t| ∧ |t| ≤ b/c}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hmem (s : ℝ) : s/c ∈ T ↔ s ∈ S := by
    simp only [T, S, Set.mem_ofPred_eq, abs_div, abs_of_pos hc, div_le_div_iff_of_pos_right hc]
  have hcomp := (hi.integrable_indicator hT).comp_mul_left' (inv_ne_zero hc.ne')
  have heq : (fun s : ℝ => T.indicator f (c⁻¹*s)) = S.indicator (fun s => f (s/c)) := by
    funext s
    rw [show c⁻¹*s = s/c by ring]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem s).mpr hs)]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun ht => hs ((hmem s).mp ht))]
  rw [heq] at hcomp
  exact (integrable_indicator_iff hS).mp hcomp

/-- Enlarging the rescaled window is legitimate for nonnegative integrable
majorants. This is the comparison used after the bilinear time rescaling. -/
theorem integral_abs_window_div_le {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    (a b A B : ℝ) {c : ℝ} (hc : 0 < c)
    (hfi : IntegrableOn f {t : ℝ | A ≤ |t| ∧ |t| ≤ B})
    (hA : A ≤ a/c) (hB : b/c ≤ B) :
    (∫ s : ℝ in {s : ℝ | a ≤ |s| ∧ |s| ≤ b}, f (s/c)) ≤
      c * ∫ t : ℝ in {t : ℝ | A ≤ |t| ∧ |t| ≤ B}, f t := by
  rw [integral_abs_window_div f a b hc]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply setIntegral_mono_set hfi (Filter.Eventually.of_forall hf)
  exact Filter.Eventually.of_forall (fun t ht => ⟨hA.trans ht.1, ht.2.trans hB⟩)

end WaveTurbulence.WeylSums
