/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! Products of variables with all finite moments are integrable on a finite measure space. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

theorem integrable_prod_of_all_memLp {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ι → Ω → ℂ) (s : Finset ι)
    (hX : ∀ i ∈ s, ∀ p : ℕ, 1 ≤ p → MemLp (X i) (p : ℝ≥0∞) μ) :
    Integrable (fun ω => ∏ i ∈ s, X i ω) μ := by
  classical
  by_cases hs : s = ∅
  · subst s
    simpa only [Finset.prod_empty] using integrable_const (1 : ℂ)
  have hcard : 1 ≤ s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hmem := MemLp.fun_prod (p := fun _ : ι => (s.card : ℝ≥0∞))
    (fun i hi => hX i hi s.card hcard)
  have h0 : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  have he : (∑ _i ∈ s, (s.card : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel h0 (by finiteness), inv_one]
  rw [he] at hmem
  exact memLp_one_iff_integrable.mp hmem

end WaveTurbulence.Induct
