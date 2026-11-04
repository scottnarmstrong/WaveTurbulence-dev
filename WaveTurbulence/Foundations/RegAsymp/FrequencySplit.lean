/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Recovering the eta time norm from the main-coefficient weights

DH23 (maincoef2) has time weight1-eta/8, while (maincoef2.5) has only
eta/4. Split at frequency size L^(4/3): the low-frequency NT error costs
one extra L^eta, and the high-frequency crude estimate gains L^(-1).
This gives precisely the source remainder exponent -gamma1+2eta.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- On low frequencies, upgrading eta/4 to eta costs at most L^eta. -/
theorem low_frequency_weight {L q η : ℝ} (hL : 1 ≤ L) (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hcut : q ≤ L ^ (4 / 3 : ℝ)) : q ^ η ≤ L ^ η * q ^ (η / 4) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hb : q ^ (3*η/4) ≤ L ^ η := by
    calc q ^ (3*η/4) ≤ (L ^ (4/3 : ℝ)) ^ (3*η/4) :=
        Real.rpow_le_rpow hq0.le hcut (by positivity)
      _ = L ^ η := by rw [← Real.rpow_mul hL0.le]; congr 1; ring
  calc q ^ η = q ^ (3*η/4) * q ^ (η/4) := by rw [← Real.rpow_add hq0]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hq0.le _)

/-- Above the cutoff, the strong time weight supplies at least L^(-1). -/
theorem high_frequency_weight {L q η : ℝ} (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hη : η ≤ 1/20) (hcut : L ^ (4/3 : ℝ) ≤ q) :
    q ^ η ≤ L ^ (-1 : ℝ) * q ^ (1-η/8) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hβ : 0 ≤ 1-9*η/8 := by linarith only [hη]
  have he : 1 ≤ (4/3 : ℝ)*(1-9*η/8) := by linarith only [hη]
  have hb : L ≤ q ^ (1-9*η/8) := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ ((4/3 : ℝ)*(1-9*η/8)) := Real.rpow_le_rpow_of_exponent_le hL he
      _ = (L ^ (4/3 : ℝ)) ^ (1-9*η/8) := Real.rpow_mul hL0.le _ _
      _ ≤ q ^ (1-9*η/8) := Real.rpow_le_rpow (Real.rpow_nonneg hL0.le _) hcut hβ
  calc q ^ η = L ^ (-1 : ℝ) * (L * q ^ η) := by rw [Real.rpow_neg_one]; field_simp
    _ ≤ L ^ (-1 : ℝ) * (q ^ (1-9*η/8) * q ^ η) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hq0.le _))
        (Real.rpow_nonneg hL0.le _)
    _ = _ := by rw [← Real.rpow_add hq0]; congr 2; ring

/-- Pointwise low/high-frequency assembly of the source remainder rate.
D is the crude derivative envelope; M is the weighted-moment envelope.
The two error bounds are applied on different frequency regimes. -/
theorem frequency_split_majorant {L q η σ E D M : ℝ}
    (hL : 1 ≤ L) (hq : 1 ≤ q) (hη0 : 0 ≤ η) (hη : η ≤ 1/20) (hσ : σ ≤ 1)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hcrude : E ≤ D) (herror : E ≤ L ^ (-σ+η) * M) :
    q ^ η * E ≤ L ^ (-σ+2*η) * (q ^ (η/4) * M + q ^ (1-η/8) * D) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hr : 0 ≤ L ^ (-σ+2*η) := Real.rpow_nonneg hL0.le _
  by_cases hc : q ≤ L ^ (4/3 : ℝ)
  · calc q ^ η * E ≤ (L ^ η * q ^ (η/4)) * (L ^ (-σ+η) * M) :=
        mul_le_mul (low_frequency_weight hL hq hη0 hc) herror hE (by positivity)
      _ = L ^ (-σ+2*η) * (q ^ (η/4) * M) := by
        rw [show (L ^ η * q ^ (η/4)) * (L ^ (-σ+η) * M) =
          (L ^ η * L ^ (-σ+η)) * (q ^ (η/4) * M) by ring,← Real.rpow_add hL0]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hr
  · have hc' : L ^ (4/3 : ℝ) ≤ q := (lt_of_not_ge hc).le
    have hrate : L ^ (-1 : ℝ) ≤ L ^ (-σ+2*η) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hσ,hη0])
    calc q ^ η * E ≤ q ^ η * D := mul_le_mul_of_nonneg_left hcrude (by positivity)
      _ ≤ (L ^ (-1 : ℝ) * q ^ (1-η/8)) * D :=
        mul_le_mul_of_nonneg_right (high_frequency_weight hL hq hη hc') hD
      _ ≤ L ^ (-σ+2*η) * (q ^ (1-η/8) * D) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hrate (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hr

end WaveTurbulence.RegAsymp
