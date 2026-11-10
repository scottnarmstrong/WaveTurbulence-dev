/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# Lattice rescaling estimates

Elementary rescaling and Euclidean bounds for TARGET Lemma A.6.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset
open scoped Classical InnerProductSpace Pointwise

/-- Euclidean norm is bounded by the sum of the absolute coordinates. -/
theorem norm_mom_le_sum_abs {d : ℕ} (x : Mom d) : ‖x‖ ≤ ∑ i, |x i| := by
  have h := sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset (Fin d)))
    (fun i _ => abs_nonneg (x i))
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

end WaveTurbulence.LinAlg
