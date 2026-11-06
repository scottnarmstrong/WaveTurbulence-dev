/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Interpolation
public import Mathlib.Analysis.SpecificLimits.Basic
/-! TARGET L2253–2255: sum class bounds by their two discrete complexity parameters. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

/-- Finite grouping, with a separate estimate for each class and for the number of classes.
The fiber cardinality is the actual finite carrier cardinality. -/
theorem norm_sum_le_counted {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (index : ι → κ) (f : ι → ℂ) (A B : κ → ℝ)
    (hmap : ∀ i ∈ s, index i ∈ t) (hA : ∀ v ∈ t, 0 ≤ A v)
    (hcount : ∀ v ∈ t, ((s.filter fun i => index i = v).card : ℝ) ≤ B v)
    (hbound : ∀ i ∈ s, ‖f i‖ ≤ A (index i)) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ v ∈ t, B v * A v := by
  classical
  rw [← sum_fiberwise_of_maps_to hmap f]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  calc
    ‖∑ i ∈ s.filter (fun i => index i = v), f i‖ ≤
        ∑ i ∈ s.filter (fun i => index i = v), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s.filter (fun i => index i = v), A v := by
      apply sum_le_sum
      intro i hi
      obtain ⟨his, hiv⟩ := mem_filter.mp hi
      simpa only [hiv] using hbound i his
    _ = ((s.filter fun i => index i = v).card : ℝ) * A v := by simp
    _ ≤ B v * A v := mul_le_mul_of_nonneg_right (hcount v hv) (hA v hv)

/-- Uniform finite geometric bound; no cutoff-dependent factor is lost. -/
theorem sum_powers_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ j ∈ range N, r ^ j ≤ 2 := by
  apply (sum_le_sum fun j _ => pow_le_pow_left₀ hr0 hr j).trans
  exact sum_geometric_two_le N

/-- The two complexity sums cost at most four once each ratio is at most one half. -/
theorem sum_two_geometric_le_four {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ 1 / 2) (hy : y ≤ 1 / 2) (G H : ℕ) :
    ∑ v ∈ (range G ×ˢ range H), x ^ v.1 * y ^ v.2 ≤ 4 := by
  rw [sum_product]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  have hG := sum_powers_le_two hx0 hx G
  have hH := sum_powers_le_two hy0 hy H
  have h0 : 0 ≤ ∑ j ∈ range H, y ^ j := sum_nonneg fun _ _ => pow_nonneg hy0 _
  nlinarith

end WaveTurbulence.LGSpine
