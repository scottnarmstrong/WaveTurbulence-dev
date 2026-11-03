/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.Estcross
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Estcross for Euclidean balls and the canonical integer lattice

DH23 `basiccount0pre` (2), `estcross` (TeX L2033–L2051). The source's balls,
inner product and integer lattice embedding appear literally in this API.
No bounded-center or fixed-level restriction is imposed on the dense strips.
-/

public section

namespace WaveTurbulence.Counting
open scoped InnerProductSpace

/-- The canonical unit lattice embedding has the actual coordinate dot product. -/
theorem inner_latticePoint_one_eq_sum {D : ℕ} (x y : Fin D → ℤ) :
    ⟪WaveTurbulence.latticePoint 1 x,WaveTurbulence.latticePoint 1 y⟫_ℝ =
      ∑ i, (x i:ℝ)*(y i:ℝ) := by
  simp [PiLp.inner_apply,WaveTurbulence.latticePoint,mul_comm]

/-- A coordinate displacement is dominated by the Euclidean displacement. -/
theorem abs_latticePoint_one_sub_coord_le_norm {D : ℕ} (x : Fin D → ℤ)
    (c : EuclideanSpace ℝ (Fin D)) (i : Fin D) :
    |(x i:ℝ)-c i| ≤ ‖WaveTurbulence.latticePoint 1 x-c‖ := by
  simpa [WaveTurbulence.latticePoint] using
    PiLp.norm_apply_le (p := (2:ENNReal)) (WaveTurbulence.latticePoint 1 x-c) i

/-- DH23 `estcross` for actual Euclidean balls, uniformly in their centers
and in the dense-strip levels. The explicit scale convention fixes the
source's implicit constants, and the logarithmic loss is the square of
`1 + log L`. All lattice points use the frozen unit-scale embedding. -/
theorem card_dense_dot_product_strips_in_balls_le {d : ℕ}
    (s : Finset (Fin (d+3) → ℤ)) (c : EuclideanSpace ℝ (Fin (d+3)))
    {rho theta L : ℝ} (hrho : 0 ≤ rho) (htheta : 1 ≤ theta)
    (hscale : 16*((3:ℝ)^(d+1)*theta) ≤ rho) (hrhoL : rho ≤ L)
    (hball : ∀ x ∈ s, ‖WaveTurbulence.latticePoint 1 x-c‖ ≤ L)
    (hdense : ∀ x ∈ s,
      ∃ Y : Finset (Fin (d+3) → ℤ), ∃ b : EuclideanSpace ℝ (Fin (d+3)), ∃ alpha : ℝ,
        (∀ y ∈ Y, ‖WaveTurbulence.latticePoint 1 y-b‖ ≤ L) ∧
        (∀ y ∈ Y,
          |⟪WaveTurbulence.latticePoint 1 x,WaveTurbulence.latticePoint 1 y⟫_ℝ-alpha| ≤ rho) ∧
        L^(d+2)/theta ≤ (Y.card:ℝ)) :
    (s.card:ℝ) ≤ ((5:ℝ)^(d+3)+(d+3)*129600*((3:ℝ)^(d+1))^3)*
      (rho^(d+3)+L^(d+1)*rho^2*theta^2*(1+Real.log L)^2) := by
  apply card_dense_dot_product_strips_le s (fun i => c i) hrho htheta hscale hrhoL
  · intro x hx i
    exact (abs_latticePoint_one_sub_coord_le_norm x c i).trans (hball x hx)
  · intro x hx
    obtain ⟨Y,b,alpha,hYball,hYstrip,hYcard⟩ := hdense x hx
    refine ⟨Y,(fun i => b i),alpha,?_,?_,hYcard⟩
    · intro y hy i
      exact (abs_latticePoint_one_sub_coord_le_norm y b i).trans (hYball y hy)
    · intro y hy
      rw [← inner_latticePoint_one_eq_sum]
      exact hYstrip y hy

end WaveTurbulence.Counting
