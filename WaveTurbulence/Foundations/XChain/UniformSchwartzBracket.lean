/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SchwartzBracketBound
public import Mathlib.Topology.Order.Compact
/-! Continuous Schwartz curves have uniform spatial decay on the source compact time interval. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem uniform_schwartz_bracket_bound {d : ℕ} (T : ℝ) (φ : ℝ → SchwartzMap (Mom d) ℝ)
    (hφ : ContinuousOn φ (Icc 0 T)) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ k, |φ t k| ≤ C * jbr k ^ (-(B : ℝ)) := by
  let S : Finset (ℕ × ℕ) := Iic (B, 0)
  let Q : SchwartzMap (Mom d) ℝ → ℝ := fun f =>
    2 ^ B * ∑ m ∈ S, SchwartzMap.seminorm ℝ m.1 m.2 f + 1
  have hQ : Continuous Q := by
    apply Continuous.add _ continuous_const
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro m _
    exact (schwartz_withSeminorms ℝ (Mom d) ℝ).continuous_seminorm m
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hQ.comp_continuousOn hφ)
  refine ⟨max C 1, le_max_right _ _, fun t ht k => ?_⟩
  have htC : Q (φ t) ≤ max C 1 := (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hw : jbr k ^ B * |φ t k| ≤ Q (φ t) := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (B, 0)) (k := B) (n := 0) le_rfl le_rfl (φ t) k
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have hs : S.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (φ t) ≤
        ∑ m ∈ S, SchwartzMap.seminorm ℝ m.1 m.2 (φ t) :=
      by
      have hs := Seminorm.finset_sup_le_sum (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) S (φ t)
      simpa only [_root_.sum_apply] using hs
    have hj := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (jbr_pos k).le (jbr_le_one_add_norm k) B) (abs_nonneg (φ t k))
    have hh := h.trans (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 ^ B))
    dsimp [Q]
    exact hj.trans (by dsimp [S] at hh; linarith)
  have hd := (le_div_iff₀ (pow_pos (jbr_pos k) B)).mpr
    (show |φ t k| * jbr k ^ B ≤ max C 1 by simpa only [mul_comm] using hw.trans htC)
  simpa only [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv] using hd

end WaveTurbulence.Induct
