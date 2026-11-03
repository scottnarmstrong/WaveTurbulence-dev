/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Exact rescaling of two-time minor-arc squares -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

private instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

/-- The source two-time window: a square with a smaller concentric square removed. -/
@[expose] def timeSquareWindow (A B : ℝ) : Set (ℝ × ℝ) :=
  {xy | A ≤ max |xy.1| |xy.2| ∧ |xy.1| ≤ B ∧ |xy.2| ≤ B}

theorem measurableSet_timeSquareWindow (A B : ℝ) : MeasurableSet (timeSquareWindow A B) := by
  dsimp [timeSquareWindow]
  measurability

theorem mem_timeSquareWindow_inv_smul (A B : ℝ) {c : ℝ} (hc : 0 < c) (xy : ℝ × ℝ) :
    c⁻¹ • xy ∈ timeSquareWindow (A/c) (B/c) ↔ xy ∈ timeSquareWindow A B := by
  simp only [timeSquareWindow, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_comm c⁻¹, ← div_eq_mul_inv, abs_div, abs_of_pos hc, max_div_div_right hc.le,
    div_le_div_iff_of_pos_right hc]

/-- The Jacobian in the two time variables is exactly `c²`. -/
theorem integral_timeSquareWindow_div (f : ℝ × ℝ → ℝ) (A B : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ xy in timeSquareWindow A B, f (xy.1/c,xy.2/c)) =
      c^2 * ∫ xy in timeSquareWindow (A/c) (B/c), f xy := by
  have heq : (timeSquareWindow A B).indicator (fun xy : ℝ × ℝ => f (xy.1/c,xy.2/c)) =
      (fun xy : ℝ × ℝ => (timeSquareWindow (A/c) (B/c)).indicator f (c⁻¹ • xy)) := by
    funext xy
    have hmem := mem_timeSquareWindow_inv_smul A B hc xy
    by_cases hxy : xy ∈ timeSquareWindow A B
    · rw [Set.indicator_of_mem hxy,Set.indicator_of_mem (hmem.mpr hxy)]
      congr 1
      ext <;> simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
    · rw [Set.indicator_of_notMem hxy,Set.indicator_of_notMem (fun h => hxy (hmem.mp h))]
  rw [← integral_indicator (measurableSet_timeSquareWindow A B),heq,
    Measure.integral_comp_inv_smul_of_nonneg volume _ hc.le,
    integral_indicator (measurableSet_timeSquareWindow (A/c) (B/c))]
  simp only [Module.finrank_prod, Module.finrank_self, one_add_one_eq_two, smul_eq_mul]

/-- Integrability is preserved by the same two-time rescaling. -/
theorem integrableOn_timeSquareWindow_div {f : ℝ × ℝ → ℝ} (A B : ℝ) {c : ℝ} (hc : 0 < c)
    (hi : IntegrableOn f (timeSquareWindow (A/c) (B/c))) :
    IntegrableOn (fun xy : ℝ × ℝ => f (xy.1/c,xy.2/c)) (timeSquareWindow A B) := by
  have hcomp := (hi.integrable_indicator (measurableSet_timeSquareWindow (A/c) (B/c))).comp_smul
    (inv_ne_zero hc.ne')
  have heq : (fun xy : ℝ × ℝ => (timeSquareWindow (A/c) (B/c)).indicator f (c⁻¹ • xy)) =
      (timeSquareWindow A B).indicator (fun xy : ℝ × ℝ => f (xy.1/c,xy.2/c)) := by
    funext xy
    have hmem := mem_timeSquareWindow_inv_smul A B hc xy
    by_cases hxy : xy ∈ timeSquareWindow A B
    · rw [Set.indicator_of_mem hxy,Set.indicator_of_mem (hmem.mpr hxy)]
      congr 1
      ext <;> simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
    · rw [Set.indicator_of_notMem hxy,Set.indicator_of_notMem (fun h => hxy (hmem.mp h))]
  rw [heq] at hcomp
  exact (integrable_indicator_iff (measurableSet_timeSquareWindow A B)).mp hcomp

end WaveTurbulence.WeylSums
