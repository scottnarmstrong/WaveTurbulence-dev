/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# VINE-B♯: sums of products over a dependent finite product of index types
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineB

theorem summable_pi_prod_dep {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} (f : ∀ i, β i → ℝ)
    (h0 : ∀ i b, 0 ≤ f i b) (hf : ∀ i, Summable (f i)) :
    Summable (fun z : (∀ i, β i) => ∏ i, f i (z i)) ∧
      ∑' z : (∀ i, β i), ∏ i, f i (z i) ≤ ∏ i, ∑' b, f i b := by
  classical
  have hle : ∀ u : Finset (∀ i, β i), ∑ z ∈ u, ∏ i, f i (z i) ≤ ∏ i, ∑' b, f i b := fun u => by
    calc ∑ z ∈ u, ∏ i, f i (z i)
        ≤ ∑ z ∈ Fintype.piFinset (fun i => u.image fun z => z i), ∏ i, f i (z i) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
            fun z _ _ => Finset.prod_nonneg fun i _ => h0 i (z i)
          rw [Fintype.mem_piFinset]
          exact fun i => Finset.mem_image_of_mem _ hz
      _ = ∏ i, ∑ b ∈ u.image fun z => z i, f i b := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ i, ∑' b, f i b :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun b _ => h0 i b)
            (fun i _ => (hf i).sum_le_tsum _ fun b _ => h0 i b)
  have hs : Summable (fun z : (∀ i, β i) => ∏ i, f i (z i)) :=
    summable_of_sum_le (fun z => Finset.prod_nonneg fun i _ => h0 i (z i)) hle
  exact ⟨hs, hs.tsum_le_of_sum_le hle⟩

end WaveTurbulence.VineB
