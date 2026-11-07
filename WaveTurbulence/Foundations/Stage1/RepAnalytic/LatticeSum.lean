/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.Partition
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # Summability of `⟨a n⟩^{-Λ}` over `ℤ^d` for `Λ > d`, and comparison of brackets -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset

theorem summable_int_one_add_rpow {a s : ℝ} (ha : 0 < a) (hs : 1 < s) :
    Summable fun m : ℤ => (1 + a * |(m : ℝ)|) ^ (-s) := by
  have hb : Summable fun m : ℤ => a ^ (-s) * |(m : ℝ)| ^ (-s) :=
    (Real.summable_abs_int_rpow hs).mul_left _
  refine Summable.of_norm_bounded_eventually hb ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hm' : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), ← Real.mul_rpow ha.le hm'.le]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)

/-- `jbr x ≥ (1 + |x_i|)/√2`. -/
theorem one_add_abs_coord_le {d : ℕ} (x : Mom d) (i : Fin d) :
    (1 + |x i|) ≤ Real.sqrt 2 * jbr x := by
  have h1 : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hj : (1 + ‖x‖) ≤ Real.sqrt 2 * jbr x := by
    unfold jbr
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [norm_nonneg x, sq_nonneg (1 - ‖x‖)]
  linarith

/-- `∑_{n ∈ ℤ^d} ⟨a n⟩^{-Λ} < ∞` for `Λ > d`. -/
theorem summable_jbr_latPt_inv {d Λ : ℕ} (hd : 1 ≤ d) (hΛ : d < Λ) :
    Summable fun n : Fin d → ℤ => ((jbr (latPt d n)) ^ Λ)⁻¹ := by
  have hs : (1 : ℝ) < (Λ : ℝ) / d := by
    rw [lt_div_iff₀ (by exact_mod_cast hd)]; exact_mod_cast (by omega : 1 * d < Λ)
  have hsum := summable_pi_prod (ι := Fin d) (β := ℤ)
    (fun _ m => (Real.sqrt 2) ^ ((Λ : ℝ) / d) * (1 + lsp d * |(m : ℝ)|) ^ (-((Λ : ℝ) / d)))
    (fun _ m => by have := lsp_pos d; positivity)
    (fun _ => (summable_int_one_add_rpow (lsp_pos d) hs).mul_left _)
  refine Summable.of_nonneg_of_le (fun n => (inv_nonneg.2 (pow_nonneg (Induct.jbr_pos _).le _))) (fun n => ?_) hsum
  have hJ := Induct.jbr_pos (latPt d n)
  set s : ℝ := (Λ : ℝ) / d with hsdef
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hper : ∀ i : Fin d, (jbr (latPt d n)) ^ (-s) ≤
      Real.sqrt 2 ^ s * (1 + lsp d * |(n i : ℝ)|) ^ (-s) := by
    intro i
    have h1 := one_add_abs_coord_le (latPt d n) i
    have hc : |(latPt d n) i| = lsp d * |(n i : ℝ)| := by
      simp [latPt, abs_mul, abs_of_pos (lsp_pos d)]
    rw [hc] at h1
    have hpos : 0 < 1 + lsp d * |(n i : ℝ)| := by have := lsp_pos d; positivity
    have h2 : (1 + lsp d * |(n i : ℝ)|) ^ s ≤ (Real.sqrt 2 * jbr (latPt d n)) ^ s :=
      Real.rpow_le_rpow hpos.le h1 (by rw [hsdef]; positivity)
    rw [Real.mul_rpow (by positivity) hJ.le] at h2
    rw [Real.rpow_neg hJ.le, Real.rpow_neg hpos.le]
    have hp1 : 0 < (1 + lsp d * |(n i : ℝ)|) ^ s := Real.rpow_pos_of_pos hpos _
    have hp2 : 0 < jbr (latPt d n) ^ s := Real.rpow_pos_of_pos hJ _
    rw [inv_le_iff_one_le_mul₀ hp2]
    calc (1 : ℝ) = (1 + lsp d * |(n i : ℝ)|) ^ s * ((1 + lsp d * |(n i : ℝ)|) ^ s)⁻¹ := by
          field_simp
      _ ≤ (Real.sqrt 2 ^ s * jbr (latPt d n) ^ s) * ((1 + lsp d * |(n i : ℝ)|) ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hp1.le)
      _ = Real.sqrt 2 ^ s * ((1 + lsp d * |(n i : ℝ)|) ^ s)⁻¹ * jbr (latPt d n) ^ s := by ring
  have hprod : ((jbr (latPt d n)) ^ Λ)⁻¹ = ∏ _i : Fin d, (jbr (latPt d n)) ^ (-s) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_natCast (jbr (latPt d n) ^ (-s)) d, ← Real.rpow_mul hJ.le,
      ← Real.rpow_natCast (jbr (latPt d n)) Λ, ← Real.rpow_neg hJ.le]
    congr 1
    rw [hsdef]
    field_simp
  rw [hprod]
  exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hJ.le (-s)) (fun i _ => hper i)

end WaveTurbulence.RepAnalytic
