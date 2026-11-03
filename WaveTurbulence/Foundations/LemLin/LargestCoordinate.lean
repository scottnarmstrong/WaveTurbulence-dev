/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.LatticeRescaling
public import Mathlib.Data.Finset.Max

/-!
# A coordinate carrying a fixed fraction of the Euclidean norm

The elementary coordinate choice used in TARGET `lemlin`.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- Some nonzero coordinate controls the norm of a nonzero momentum. -/
theorem exists_large_coordinate {d : ℕ} (r : Mom d) (hr : r ≠ 0) :
    ∃ i : Fin d, 0 < |r i| ∧ ‖r‖ ≤ d * |r i| := by
  have hd : 0 < d := by
    by_contra h
    have hd : d = 0 := by omega
    subst d
    apply hr
    ext i
    exact Fin.elim0 i
  obtain ⟨i, _, hi⟩ := (univ : Finset (Fin d)).exists_max_image (fun j => |r j|)
    ⟨⟨0, hd⟩, mem_univ _⟩
  have hn : ‖r‖ ≤ d * |r i| := calc
    _ ≤ ∑ j, |r j| := LinAlg.norm_mom_le_sum_abs r
    _ ≤ ∑ _j : Fin d, |r i| := sum_le_sum (fun j hj => hi j hj)
    _ = _ := by simp
  refine ⟨i, ?_, hn⟩
  by_contra h
  have hz : |r i| = 0 := le_antisymm (le_of_not_gt h) (abs_nonneg _)
  have hnorm : ‖r‖ = 0 := le_antisymm (by simpa only [hz, mul_zero] using hn) (norm_nonneg _)
  exact hr (norm_eq_zero.mp hnorm)

end WaveTurbulence.LemLin
