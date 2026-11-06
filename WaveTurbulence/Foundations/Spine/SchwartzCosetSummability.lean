/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
/-! Schwartz profiles and finite remainder norms supply the input-coset summability
used for the actual garden kernels; it is not an additional source premise. -/
public section
open WaveTurbulence.Induct
namespace WaveTurbulence.LGSpine
open Finset

theorem exists_schwartz_jbr_decay {d : ℕ} (f : SchwartzMap (Mom d) ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, |f k| ≤ C * jbr k ^ (-(s : ℝ)) := by
  let C : ℝ := max 0 (2 ^ s * (Finset.Iic (s, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f)
  refine ⟨C, le_max_left _ _, fun k => ?_⟩
  have hbr : jbr k ≤ 1 + ‖k‖ := by
    unfold jbr
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg k]
  have hw : jbr k ^ s * |f k| ≤ C := by
    calc
      _ ≤ (1 + ‖k‖) ^ s * |f k| := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (jbr_pos k).le hbr s) (abs_nonneg _)
      _ ≤ 2 ^ s * (Finset.Iic (s, 0)).sup
          (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
        simpa using SchwartzMap.one_add_le_sup_seminorm_apply
          (m := (s, 0)) (k := s) (n := 0) (𝕜 := ℝ) le_rfl le_rfl f k
      _ ≤ C := le_max_right _ _
  rw [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (jbr_pos k) _)).mpr (by simpa only [mul_comm] using hw)

theorem summable_abs_schwartz_coset {d : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (f : SchwartzMap (Mom d) ℝ) (k : Mom d) :
    Summable (fun n : Fin d → ℤ => |f (k + latticePoint L n)|) := by
  obtain ⟨C, _, hC⟩ := exists_schwartz_jbr_decay f (d + 1)
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun n => ?_) ((summable_jbr_coset_neg hL k).mul_left C)
  simpa only [Nat.cast_add, Nat.cast_one] using hC (k + latticePoint L n)

/-- For every stage whose remainder norm has enough weight, the literal F_r input is summable. -/
theorem summable_abs_inputsF_coset (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (hL : 1 ≤ P.L) (r : ℕ) (hweight : P.d + 1 ≤ P.Lambda r)
    (hR : SNormR (P.Lambda r) (P.Lambda r) (R r) ≤ ENNReal.ofReal (P.L ^ (-P.theta r)))
    (k : Mom P.d) :
    Summable (fun n : Fin P.d → ℤ => |inputsF P R r (k + latticePoint P.L n)|) := by
  have hφ := summable_abs_schwartz_coset hL (P.φ (P.δ * r)) k
  have hrem := summable_abs_coset_of_SNormR hL hweight
    (Real.rpow_nonneg (by linarith : 0 ≤ P.L) _) (R r) hR k
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun n => abs_add_le _ _) (hφ.add hrem)

end WaveTurbulence.LGSpine
