/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzSeries
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Convergence of seminorm-absolutely-summable series in the actual Schwartz topology
-/

public section

noncomputable section

open Filter
open scoped SchwartzMap Topology

namespace WaveTurbulence.WKEL2

variable {d : ℕ} {F : ℕ → 𝓢(Mom d, ℝ)}

/-- Every shifted tail retains absolute summability in every defining seminorm. -/
theorem summable_seminorm_shift
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j)))
    (N q n : ℕ) : Summable (fun j => SchwartzMap.seminorm ℝ q n (F (j + N))) :=
  (summable_nat_add_iff N).2 (hF q n)

/-- Each actual pointwise scalar series is absolutely summable. -/
theorem summable_schwartzSeries_apply
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) (k : Mom d) :
    Summable (fun j => F j k) :=
  Summable.of_norm_bounded (hF 0 0) (fun j => SchwartzMap.norm_le_seminorm ℝ (F j) k)

/-- The difference from a partial sum is exactly the actual Schwartz tail series. -/
theorem schwartzSeries_sub_partialSum
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) (N : ℕ) :
    schwartzSeries F hF - ∑ j ∈ Finset.range N, F j =
      schwartzSeries (fun j => F (j + N)) (summable_seminorm_shift hF N) := by
  ext k
  simp only [sub_apply, schwartzSeries_apply, _root_.sum_apply]
  rw [← (summable_schwartzSeries_apply hF k).sum_add_tsum_nat_add N]
  ring

/-- Absolute convergence in every Schwartz seminorm gives convergence in the defining topology. -/
theorem tendsto_schwartzSeries_partialSums
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, F j) atTop (𝓝 (schwartzSeries F hF)) := by
  apply ((schwartz_withSeminorms ℝ (Mom d) ℝ).tendsto_nhds _ _).2
  rintro ⟨q, n⟩ ε hε
  have H := tendsto_sum_nat_add (fun j => SchwartzMap.seminorm ℝ q n (F j))
  filter_upwards [H.eventually (gt_mem_nhds hε)] with N hN
  change SchwartzMap.seminorm ℝ q n ((∑ j ∈ Finset.range N, F j) - schwartzSeries F hF) < ε
  have hneg : (∑ j ∈ Finset.range N, F j) - schwartzSeries F hF =
      -(schwartzSeries F hF - ∑ j ∈ Finset.range N, F j) := by abel
  rw [hneg, map_neg_eq_map, schwartzSeries_sub_partialSum]
  exact (seminorm_schwartzSeries_le (F := fun j => F (j + N))
    (summable_seminorm_shift hF N) q n).trans_lt hN

end WaveTurbulence.WKEL2
