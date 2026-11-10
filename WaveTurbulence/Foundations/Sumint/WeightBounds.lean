/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
import Mathlib.Tactic

/-!
# Consequences of the exact snapshot-5 weight hypothesis

Finite positive-order S norms provide the classical regularity required
for localization. The zeroth multiindex gives the literal spatial decay,
without adding a separate weight assumption.
-/

public section

open Finset
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Finite positive-order draft S norm forces exactly the drafted regularity. -/
theorem contDiff_of_SNorm_le {d N K : ℕ} (hN : N ≠ 0) {F : Mom d → ℂ}
    {B : ℝ} (hF : SNorm N K F ≤ ENNReal.ofReal B) : ContDiff ℝ N F := by
  classical
  by_contra hr
  have he : SNorm N K F = ⊤ := by simp [SNorm, hN, hr]
  rw [he] at hF
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hF

/-- The zeroth multiindex is the original function. -/
theorem iterPartial_zero {d : ℕ} (F : Mom d → ℂ) : iterPartial (0 : Fin d → ℕ) F = F := by
  unfold iterPartial
  have h (l : List (Fin d)) : l.foldr (fun j G => (partialMom j)^[((0 : Fin d → ℕ) j)] G) F = F := by
    induction l with
    | nil => rfl
    | cons j l ih => simpa only [List.foldr_cons, Pi.zero_apply, Function.iterate_zero, id_eq] using ih
  exact h _

/-- The draft norm controls every permitted weighted coordinate derivative. -/
theorem weighted_multiindex_norm_le_of_SNorm_le {d N K : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (ρ : Fin d → ℕ) (hρ : ∑ j, ρ j ≤ N) (x : Mom d) :
    jbr x ^ K * ‖iterPartial ρ F x‖ ≤ B := by
  classical
  have hfinite : SNorm N K F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF
  have hguard : N = 0 ∨ ContDiff ℝ N F := by
    by_contra hn
    exact hfinite (by simp [SNorm, hn])
  have he : SNorm N K F =
      ⨆ (σ : Fin d → ℕ) (_ : ∑ j, σ j ≤ N) (k : Mom d),
        ENNReal.ofReal (jbr k ^ K * ‖iterPartial σ F k‖) := by simp only [SNorm, ite_eq_left hguard]
  rw [he] at hF
  have hs := (iSup_le_iff.mp hF) ρ
  have hp := (iSup_le_iff.mp hs) hρ
  have hx := (iSup_le_iff.mp hp) x
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hx

/-- The zeroth word gives the literal decay of the weight. -/
theorem weighted_norm_le_of_SNorm_le {d N K : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) (x : Mom d) :
    jbr x ^ K * ‖F x‖ ≤ B := by
  simpa only [iterPartial_zero] using
    weighted_multiindex_norm_le_of_SNorm_le hB hF (0 : Fin d → ℕ) (by simp) x

/-- The scalar weight is at least one at every momentum. -/
theorem one_le_jbr {d : ℕ} (x : Mom d) : 1 ≤ jbr x := by
  unfold jbr
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ‖x‖]

end WaveTurbulence.Sumint
