/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearPointwise

/-! # Time measurability without time derivatives -/

public section
open Finset MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Measurability of a lattice series with a fixed finite support. -/
theorem measurable_finite_amplitude_sum {α X : Type*} [MeasurableSpace X]
    (A : α → ℂ) (hA : (Function.support A).Finite) (f : X → α → ℂ)
    (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => ∑' a, A a*f x a) := by
  classical
  let S := hA.toFinset
  have heq (x : X) : (∑' a, A a*f x a) = ∑ a ∈ S, A a*f x a := by
    apply tsum_eq_sum
    intro a ha
    have hz : A a = 0 := by
      by_contra hh
      exact ha (hA.mem_toFinset.mpr hh)
    rw [hz, zero_mul]
  simp_rw [heq]
  exact Finset.measurable_sum _ (fun a ha => measurable_const.mul (hf a))

/-- Rewriting a width-scaled cutoff as an ordinary lattice cutoff. -/
theorem scaled_latticePoint_sub {d : ℕ} {L width : ℝ} (hL : L ≠ 0) (hw : width ≠ 0)
    (n : Fin d → ℤ) (a : Mom d) :
    width⁻¹ • (latticePoint L n-a) = latticePoint (L*width) n-width⁻¹ • a := by
  ext j
  simp only [latticePoint, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [hL,hw]

/-- The source sum is measurable whenever each spatial sample of the
amplitude is measurable in time. No time derivative is imposed. -/
theorem measurable_weightedBilinearLatticeSum {d : ℕ} {L width : ℝ}
    (hL : 0 < L) (hw : 0 < width) (Φ : ℝ → Mom d → Mom d → ℂ)
    (hΦ : ∀ x y, Measurable (fun s => Φ s x y)) (a b ξ ζ : Mom d) :
    Measurable (fun s => weightedBilinearLatticeSum Φ L width s a b ξ ζ) := by
  let A (q : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
    (latticeCutoff (width⁻¹ • (latticePoint L q.1-a))*
      latticeCutoff (width⁻¹ • (latticePoint L q.2-b)) : ℝ)
  have hA : (Function.support A).Finite := by
    have hh := finite_support_bilinear (mul_pos hL hw) (width⁻¹ • a) (width⁻¹ • b) (fun _ => 1)
    simpa only [A, scaled_latticePoint_sub hL.ne' hw.ne', mul_one] using hh
  have hh := measurable_finite_amplitude_sum A hA
    (fun s q => Φ s (latticePoint L q.1) (latticePoint L q.2) *
      e (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ζ +
        s*inner ℝ (latticePoint L q.1) (latticePoint L q.2)))
    (fun q => (hΦ _ _).mul (continuous_e.measurable.comp (by fun_prop)))
  simpa only [weightedBilinearLatticeSum, A, mul_assoc] using hh

end WaveTurbulence.WeylSums
