/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Termwise differentiation of series within a convex set

`hasFDerivWithinAt_tsum_of_convex`: if `Tₙ` has derivative `T'ₙ x` within a convex set `s` at every
point of `s`, with `‖T'ₙ x‖ ≤ uₙ` on `s` and `∑ uₙ < ∞`, and `∑ₙ Tₙ x` converges on `s`, then
`x ↦ ∑ₙ Tₙ x` has derivative `D` within `s` at every point of `s`, where `D v = ∑ₙ T'ₙ x v`.

Mathlib's `hasFDerivAt_tsum` covers open sets only; the within version on the closed slab
`[0, T] × ℝ^d` is what the smoothness of NLS solutions on a closed time interval needs. The proof
splits the series into a finite part (differentiable termwise) and a tail controlled by the mean
value inequality on the convex set.
-/

public section

noncomputable section

open Set Filter Topology

namespace WaveTurbulence.NLS

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Termwise differentiation of a series within a convex set. -/
theorem hasFDerivWithinAt_tsum_of_convex {s : Set E} (hs : Convex ℝ s) {T : α → E → F}
    {T' : α → E → E →L[ℝ] F} {u : α → ℝ} (hu : Summable u)
    (hT : ∀ n, ∀ x ∈ s, HasFDerivWithinAt (T n) (T' n x) s x)
    (hT' : ∀ n, ∀ x ∈ s, ‖T' n x‖ ≤ u n) (hsum : ∀ x ∈ s, Summable fun n => T n x)
    {x : E} (hx : x ∈ s) {D : E →L[ℝ] F} (hD : ∀ v, HasSum (fun n => T' n x v) (D v)) :
    HasFDerivWithinAt (fun y => ∑' n, T n y) D s x := by
  refine HasFDerivWithinAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun ε hε => ?_)
  have hu0 : ∀ n, 0 ≤ u n := fun n => (norm_nonneg _).trans (hT' n x hx)
  -- a finite set carrying all but `ε/4` of `∑ u`
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 (ε / 4)
    (by positivity)).exists
  set ε' := ε / (2 * (N.card + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hfin : ∀ᶠ y in 𝓝[s] x, ∀ n ∈ N,
      ‖T n y - T n x - T' n x (y - x)‖ ≤ ε' * ‖y - x‖ := by
    rw [Filter.eventually_all_finset]
    intro n _
    exact (hT n x hx).isLittleO.bound hε'0
  filter_upwards [hfin, self_mem_nhdsWithin] with y hy hys
  set R : α → F := fun n => T n y - T n x - T' n x (y - x) with hR
  have hRsum : HasSum R ((∑' n, T n y) - (∑' n, T n x) - D (y - x)) :=
    ((hsum y hys).hasSum.sub (hsum x hx).hasSum).sub (hD (y - x))
  have hRle : ∀ n, ‖R n‖ ≤ 2 * u n * ‖y - x‖ := by
    intro n
    have hmv := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => T n z - T' n x z) (f' := fun z => T' n z - T' n x) (C := u n + u n)
      (fun z hz => (hT n z hz).sub (T' n x).hasFDerivWithinAt)
      (fun z hz => (norm_sub_le _ _).trans (by linarith [hT' n z hz, hT' n x hx])) hx hys
    calc ‖R n‖ = ‖(T n y - T' n x y) - (T n x - T' n x x)‖ := by
          rw [hR]; simp only [map_sub]; congr 1; abel
      _ ≤ (u n + u n) * ‖y - x‖ := hmv
      _ = 2 * u n * ‖y - x‖ := by ring
  have hRn : Summable fun n => ‖R n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hRle ((hu.mul_left 2).mul_right _)
  rw [← hRsum.tsum_eq]
  calc ‖∑' n, R n‖ ≤ ∑' n, ‖R n‖ := norm_tsum_le_tsum_norm hRn
    _ = ∑ n ∈ N, ‖R n‖ + ∑' n : ↥((N : Set α)ᶜ), ‖R n‖ := (hRn.sum_add_tsum_compl).symm
    _ ≤ ∑ _n ∈ N, ε' * ‖y - x‖ + ∑' n : ↥((N : Set α)ᶜ), 2 * u n * ‖y - x‖ :=
        add_le_add (Finset.sum_le_sum fun n hn => hy n hn)
          (Summable.tsum_le_tsum (f := fun n : ↥((N : Set α)ᶜ) => ‖R n‖)
            (g := fun n : ↥((N : Set α)ᶜ) => 2 * u n * ‖y - x‖) (fun n => hRle n)
            (hRn.subtype _) (((hu.mul_left 2).mul_right _).subtype _))
    _ = (N.card * ε') * ‖y - x‖ + 2 * (∑' n : ↥((N : Set α)ᶜ), u n) * ‖y - x‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, tsum_mul_right, tsum_mul_left]
        ring
    _ ≤ (ε / 2) * ‖y - x‖ + 2 * (ε / 4) * ‖y - x‖ := by
        gcongr
        · rw [hε']
          have hc : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        · exact hN.le
    _ = ε * ‖y - x‖ := by ring

end WaveTurbulence.NLS
