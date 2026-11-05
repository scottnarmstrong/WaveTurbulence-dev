/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! Pointwise weighted control is a direct consequence of the draft spatial norm. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem iterPartial_zero_index {d : ℕ} (F : Mom d → ℂ) : iterPartial (fun _ => 0) F = F := by
  unfold iterPartial
  have h : ∀ l : List (Fin d), l.foldr (fun j G => (partialMom j)^[0] G) F = F := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih => exact ih
  exact h _

theorem SNorm_pointwise {d A B : ℕ} (F : Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    jbr k ^ B * ‖F k‖ ≤ C := by
  classical
  have hbound : ENNReal.ofReal (jbr k ^ B * ‖F k‖) ≤ SNorm A B F := by
    unfold SNorm
    split_ifs
    · have hz : (∑ _ : Fin d, (0 : ℕ)) ≤ A := by simp
      have hi : ENNReal.ofReal (jbr k ^ B * ‖iterPartial (fun _ => 0) F k‖) ≤
          ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ A) (x : Mom d),
            ENNReal.ofReal (jbr x ^ B * ‖iterPartial ρ F x‖) :=
        le_iSup_of_le (fun _ : Fin d => (0 : ℕ))
        (le_iSup_of_le hz (le_iSup_of_le k le_rfl))
      simpa only [iterPartial_zero_index] using hi
    · exact le_top
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hbound.trans h)

theorem SNormR_pointwise {d A B : ℕ} (F : Mom d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNormR A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    |F k| ≤ C * jbr k ^ (-(B : ℝ)) := by
  have hb : jbr k ^ B * |F k| ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      SNorm_pointwise (fun x => (F x : ℂ)) C hC h k
  have hpos : 0 < jbr k ^ B := pow_pos (jbr_pos k) B
  have hd : |F k| ≤ C / (jbr k ^ B) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
  simpa only [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv] using hd

end WaveTurbulence.Induct
