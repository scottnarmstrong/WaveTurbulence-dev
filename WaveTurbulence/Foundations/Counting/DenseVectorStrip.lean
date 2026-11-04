/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DenseProductStrip
public import WaveTurbulence.Foundations.Counting.LatticeCoordinates
import Mathlib.Tactic

/-!
# Short relations from full-dimensional integer strips

DH23 `estcross`: the actual coordinate dot product is split into its first
two terms and the remaining terms, and the proved finite-fiber density
argument supplies the integer relation. No planar slice is assumed.
-/

public section

namespace WaveTurbulence.Counting

/-- Full-dimensional version of the short-relation density lemma for the
first two coordinates, uniformly in the center and in the level. -/
theorem exists_small_relation_of_dense_vector_strip {d : ℕ}
    (s : Finset (Fin (d+2) → ℤ)) (x c : Fin (d+2) → ℝ)
    {alpha rho theta L : ℝ}
    (hrho : 0 ≤ rho) (htheta : 1 ≤ theta) (hL : 16*((3:ℝ)^d*theta) ≤ L)
    (ha : 2*rho < |x 0|) (hb : |x 1| ≤ |x 0|)
    (hbox : ∀ n ∈ s, ∀ i, |(n i:ℝ)-c i| ≤ L)
    (hstrip : ∀ n ∈ s, |(∑ i, x i*(n i:ℝ))-alpha| ≤ rho)
    (hdense : L^(d+1)/theta ≤ (s.card:ℝ)) :
    ∃ m n : ℤ, n ≠ 0 ∧ |(n:ℝ)| ≤ 8*((3:ℝ)^d*theta) ∧
      |(m:ℝ)| ≤ 9*((3:ℝ)^d*theta) ∧ |x 0*(m:ℝ)+x 1*(n:ℝ)| ≤ 2*rho := by
  classical
  let t := s.map (latticeSplitTwo d).toEmbedding
  apply exists_small_relation_of_dense_product_strip t
    (fun z => ∑ i : Fin d, x i.succ.succ*(z i:ℝ)) (fun i => c i.succ.succ)
    (a := x 0) (b := x 1) (alpha := alpha) (v := c 1) hrho htheta hL ha hb
  · intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hp
    exact hbox n hn 1
  · intro p hp i
    obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hp
    exact hbox n hn i.succ.succ
  · intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_map.mp hp
    have hh := hstrip n hn
    rw [sum_coordinate_mul_split_two] at hh
    exact hh
  · simpa only [t,Finset.card_map] using hdense

end WaveTurbulence.Counting
