/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Every real Schwartz input has a uniform weighted Japanese-bracket bound. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem jbr_le_one_add_norm {d : ℕ} (k : Mom d) : jbr k ≤ 1 + ‖k‖ := by
  unfold jbr
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg k]

theorem schwartz_exists_bracket_bound {d : ℕ} (f : SchwartzMap (Mom d) ℝ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, |f k| ≤ C * jbr k ^ (-(B : ℝ)) := by
  let C : ℝ := 2 ^ B * (Iic (B, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun k => ?_⟩
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (B, 0)) (k := B) (n := 0) le_rfl le_rfl f k
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hs
  have hw : jbr k ^ B * |f k| ≤ C := by
    have hp := pow_le_pow_left₀ (jbr_pos k).le (jbr_le_one_add_norm k) B
    exact (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans
      (hs.trans (by dsimp [C]; linarith))
  have hd := (le_div_iff₀ (pow_pos (jbr_pos k) B)).mpr
    (show |f k| * jbr k ^ B ≤ C by simpa only [mul_comm] using hw)
  simpa only [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv] using hd

end WaveTurbulence.Induct
