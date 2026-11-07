/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.LocalizationBox
import Mathlib.Tactic

/-!
# A dimension-only overlap bound for the localization cubes

At any fixed momentum at most `4^d` of the closed support boxes can meet.
The explicit active set also covers boundary points and all derivatives
of the partition pieces.
-/

@[expose] public section
set_option autoImplicit false

open Finset
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Closed cube membership implies membership in the landed finite active set. -/
theorem mem_thetaSupport_of_mem_localizationBox {d : ℕ} {a : Fin d → ℤ} {x : Mom d}
    (hx : x ∈ localizationBox a) : a ∈ ApproxNT.thetaSupport ((2 : ℝ) • x) := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  change a i ∈ (Finset.range 4).image (fun j : ℕ => ⌊2 * x i⌋ - 1 + (j : ℤ))
  have hlow : (a i : ℝ) / 2 - 1 / 2 ≤ x i := hx.1 i
  have hupp : x i ≤ (a i : ℝ) / 2 + 1 / 2 := hx.2 i
  have hf0 := Int.floor_le (2 * x i)
  have hf1 := Int.lt_floor_add_one (2 * x i)
  have ha0R : (⌊2 * x i⌋ : ℝ) - 1 ≤ (a i : ℝ) := by linarith
  have ha1R : (a i : ℝ) ≤ (⌊2 * x i⌋ : ℝ) + 2 := by linarith
  have ha0 : ⌊2 * x i⌋ - 1 ≤ a i := by exact_mod_cast ha0R
  have ha1 : a i ≤ ⌊2 * x i⌋ + 2 := by exact_mod_cast ha1R
  refine Finset.mem_image.mpr ⟨(a i - (⌊2 * x i⌋ - 1)).toNat, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    omega
  · omega

/-- The explicit set of potentially active centers has at most `4^d` elements. -/
theorem card_thetaSupport_le {d : ℕ} (x : Mom d) : (ApproxNT.thetaSupport x).card ≤ 4 ^ d := by
  classical
  rw [ApproxNT.thetaSupport, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 4 := by
      apply Finset.prod_le_prod
      intro i _
      exact (Finset.card_image_le).trans (by simp)
    _ = _ := by simp

/-- An extended norm sum over the localization family costs only its finite overlap. -/
theorem tsum_enorm_le_localization_overlap {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (G : (Fin d → ℤ) → E) (x : Mom d) {C : ℝ}
    (hzero : ∀ a, x ∉ localizationBox a → G a = 0)
    (hbound : ∀ a, ‖G a‖ ≤ C) :
    (∑' a, ‖G a‖ₑ) ≤ ENNReal.ofReal ((4 : ℝ) ^ d) * ENNReal.ofReal C := by
  classical
  let s := ApproxNT.thetaSupport ((2 : ℝ) • x)
  have hz (a : Fin d → ℤ) (ha : a ∉ s) : G a = 0 :=
    hzero a (fun hx => ha (mem_thetaSupport_of_mem_localizationBox hx))
  rw [tsum_eq_sum (s := s) (fun a ha => by rw [hz a ha, enorm_zero])]
  calc
    _ ≤ ∑ _a ∈ s, ENNReal.ofReal C := by
      apply Finset.sum_le_sum
      intro a _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound a)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal C := by simp
    _ ≤ _ := by
      apply mul_le_mul_left
      have hc : s.card ≤ 4 ^ d := card_thetaSupport_le ((2 : ℝ) • x)
      have hh : (s.card : ℝ≥0∞) ≤ ((4 ^ d : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hc
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh

end WaveTurbulence.SumintPar
