/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AllMoments
/-! Products retain all finite moments, with the Hölder exponents chosen explicitly. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

theorem memLp_prod_of_all_memLp {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ι → Ω → ℂ) (s : Finset ι)
    (hX : ∀ i ∈ s, ∀ p : ℕ, 1 ≤ p → MemLp (X i) (p : ℝ≥0∞) μ)
    (q : ℕ) (hq : 1 ≤ q) : MemLp (fun ω => ∏ i ∈ s, X i ω) (q : ℝ≥0∞) μ := by
  classical
  by_cases hs : s = ∅
  · subst s
    simpa only [prod_empty] using (memLp_const (1 : ℂ) (p := (q : ℝ≥0∞)))
  have hcard : 1 ≤ s.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hs)
  have hmem := MemLp.fun_prod (p := fun _ : ι => ((s.card * q : ℕ) : ℝ≥0∞))
    (fun i hi => hX i hi (s.card * q) (Nat.mul_pos (by omega) (by omega)))
  have hc : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  have he : (∑ _i ∈ s, ((s.card * q : ℕ) : ℝ≥0∞)⁻¹)⁻¹ = (q : ℝ≥0∞) := by
    rw [sum_const, nsmul_eq_mul, Nat.cast_mul]
    have hi : (s.card : ℝ≥0∞) * ((s.card : ℝ≥0∞) * q)⁻¹ = (q : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hc) (Or.inl (by finiteness)), ← mul_assoc, ENNReal.mul_inv_cancel hc (by finiteness), one_mul]
    rw [hi, inv_inv]
  rw [he] at hmem
  exact hmem

end WaveTurbulence.Induct
