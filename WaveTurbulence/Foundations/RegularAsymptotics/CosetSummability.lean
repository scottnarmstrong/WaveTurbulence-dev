/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Summability of the actual Schwartz inputs on any shifted momentum lattice. -/
public section
namespace WaveTurbulence.LGSpine

open WaveTurbulence.Induct

/-- Shifting the lattice costs a finite Peetre factor, with no restriction on the shift. -/
theorem jbr_coset_neg_le {d : ℕ} (L : ℝ) (k : Mom d) (n : Fin d → ℤ) :
    jbr (k + latticePoint L n) ^ (-((d : ℝ) + 1)) ≤
      (Real.sqrt 2 * jbr k) ^ (d + 1) * jbr (latticePoint L n) ^ (-((d : ℝ) + 1)) := by
  have hp := jbr_add_le (-k) (k + latticePoint L n)
  rw [neg_add_cancel_left, jbr_neg] at hp
  have hC : 0 < Real.sqrt 2 * jbr k := mul_pos (by positivity) (jbr_pos k)
  have ha := jbr_pos (latticePoint L n)
  have hb := jbr_pos (k + latticePoint L n)
  rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring]
  simp only [Real.rpow_neg (by positivity : 0 ≤ jbr (k + latticePoint L n)),
    Real.rpow_neg ha.le, Real.rpow_natCast]
  calc
    (jbr (k + latticePoint L n) ^ (d + 1))⁻¹ =
        (Real.sqrt 2 * jbr k) ^ (d + 1) *
          (((Real.sqrt 2 * jbr k) * jbr (k + latticePoint L n)) ^ (d + 1))⁻¹ := by
      rw [mul_pow (Real.sqrt 2 * jbr k), mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hC.ne'), one_mul]
    _ ≤ (Real.sqrt 2 * jbr k) ^ (d + 1) * (jbr (latticePoint L n) ^ (d + 1))⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC.le _)
      exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hp _)

theorem summable_jbr_coset_neg {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    Summable (fun n : Fin d → ℤ => jbr (k + latticePoint L n) ^ (-((d : ℝ) + 1))) :=
  Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (jbr_pos _).le _)
    (jbr_coset_neg_le L k) ((summable_jbr_rpow_neg hL).mul_left _)

/-- Finite source spatial norm supplies the exact summability hypothesis used in kernel continuity. -/
theorem summable_abs_coset_of_SNormR {d A B : ℕ} {L C : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (hC : 0 ≤ C) (F : Mom d → ℝ)
    (hF : SNormR A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    Summable (fun n : Fin d → ℤ => |F (k + latticePoint L n)|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun n => (SNormR_pointwise F C hC hF _).trans ?_)
    ((summable_jbr_coset_neg hL k).mul_left C)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr _)
  exact_mod_cast (neg_le_neg (show (d : ℝ) + 1 ≤ (B : ℝ) by exact_mod_cast hB))

end WaveTurbulence.LGSpine
