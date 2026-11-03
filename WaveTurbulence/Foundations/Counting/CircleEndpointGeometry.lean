/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointBlocks
public import WaveTurbulence.Foundations.Counting.CircleOctantPhase
import Mathlib.Tactic

/-!
# The source interval for nonempty circular endpoint blocks

Every outer-octant endpoint distance is below R/3. Hence a nonempty dyadic
block `[U,2U]` automatically has `3U<=R`, the standing localization condition
of the shared circle B-process. Empty blocks require no analytic estimate.
-/

public section

namespace WaveTurbulence.Counting

/-- Every outer-octant column has endpoint distance below one third of R. -/
theorem circle_octant_endpoint_distance_lt_third {R c x : ℝ} (hR : 0 < R)
    (houter : R/Real.sqrt 2 < |x-c|) : R-|x-c| < R/3 := by
  have hspos : 0 < Real.sqrt (2:ℝ) := by positivity
  have hs : Real.sqrt (2:ℝ) ≤ 3/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hbase : 2*R/3 ≤ R/Real.sqrt 2 := by
    apply (le_div_iff₀ hspos).mpr
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*R/3)
    nlinarith only [hm]
  linarith only [hbase,houter]

/-- The actual height in terms of the unsigned endpoint distance. -/
theorem circleHeight_endpoint_distance_identity (R c x : ℝ) :
    circleHeight R c x = Real.sqrt (2*R*(R-|x-c|)-(R-|x-c|)^2) := by
  unfold circleHeight
  congr 1
  nlinarith only [sq_abs (x-c)]

/-- Nonempty actual dyadic outer-cap blocks automatically meet the circle
source localization condition. No condition on the integer center is used. -/
theorem circle_endpoint_block_empty_or_source_range {R c : ℝ} (hR : 0 < R) (m : ℕ) :
    ((integerInterval (c-R) (c+R)).filter (fun x : ℤ =>
      R/Real.sqrt 2 < |(x:ℝ)-c| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c| ∧
        R-|(x:ℝ)-c| ≤ R/(2:ℝ)^m)) = ∅ ∨ 3*(R/(2:ℝ)^(m+1)) ≤ R := by
  classical
  by_cases hempty : ((integerInterval (c-R) (c+R)).filter (fun x : ℤ =>
      R/Real.sqrt 2 < |(x:ℝ)-c| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c| ∧
        R-|(x:ℝ)-c| ≤ R/(2:ℝ)^m)) = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨_,houter,hlo,_⟩ := Finset.mem_filter.mp hx
    have hdist := circle_octant_endpoint_distance_lt_third hR houter
    linarith only [hdist,hlo]

end WaveTurbulence.Counting
