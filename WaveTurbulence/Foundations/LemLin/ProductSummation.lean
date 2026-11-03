/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Nonnegative sums over finite products

Bounding a finite family by its coordinate rectangle proves summability and
the product bound without ever relying on the totalized value of a divergent
series. Used twice in the tensorized TARGET `lemcubic0` estimate.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- Products of nonnegative summable factors have summable product-index sums. -/
theorem summable_pi_product {d : ℕ} {α : Fin d → Type*} (f : ∀ i, α i → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) (B : Fin d → ℝ)
    (hB : ∀ i, (∑' x, f i x) ≤ B i) :
    Summable (fun n : ∀ i, α i => ∏ i, f i (n i)) ∧
      (∑' n : ∀ i, α i, ∏ i, f i (n i)) ≤ ∏ i, B i := by
  have hfinite (u : Finset (∀ i, α i)) : (∑ n ∈ u, ∏ i, f i (n i)) ≤ ∏ i, B i := by
    let t : ∀ i, Finset (α i) := fun i => u.image (fun n => n i)
    calc
      _ ≤ ∑ n ∈ Fintype.piFinset t, ∏ i, f i (n i) :=
        sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr (fun i => mem_image_of_mem _ hn))
          (fun n _ _ => prod_nonneg (fun i _ => hf0 i _))
      _ = ∏ i, ∑ x ∈ t i, f i x := (prod_univ_sum t f).symm
      _ ≤ ∏ i, B i := prod_le_prod₀
        (fun i _ => sum_nonneg (fun x _ => hf0 i x))
        (fun i _ => ((hf i).sum_le_tsum (t i) (fun x _ => hf0 i x)).trans (hB i))
  have hs := summable_of_sum_le (fun n => prod_nonneg (fun i _ => hf0 i _)) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

end WaveTurbulence.LemLin
