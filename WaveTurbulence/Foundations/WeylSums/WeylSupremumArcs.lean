/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremum
public import WaveTurbulence.Foundations.WeylSums.RealArcCover

/-! # A rational-arc majorant for the full Weyl supremum -/

public section
open Finset
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- The log-free Gauss bound holds after taking both suprema. -/
theorem exists_weylSupremum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L t : ℝ) (a : ℤ) (q : ℕ), 1 ≤ L →
      1 ≤ q → (q : ℝ) ≤ L → a.natAbs.Coprime q →
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L) →
      weylSupremum L t ≤ C * L / (Real.sqrt q * (1 + L * Real.sqrt |t - (a : ℝ) / q|)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_smoothGaussSum_le weylCutoff
    weylCutoff_hasCompactSupport weylCutoff_contDiff
  refine ⟨C, hC, ?_⟩
  intro L t a q hL hq hqL ha herr
  apply ciSup_le
  intro r
  exact hb L t r 0 a q hL hq hqL ha herr

/-- A finite integrable envelope bounds the power of the supremum, at real scale. -/
theorem exists_weylSupremum_arc_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L p t : ℝ), 1 ≤ L → 0 ≤ p → t ∈ Set.Icc (0 : ℝ) 1 →
      weylSupremum L t ^ p ≤ (C * L) ^ p * rationalArcEnvelope L (p / 2) ⌊L⌋₊ t := by
  obtain ⟨C, hC, hb⟩ := exists_weylSupremum_bound
  refine ⟨C, hC, ?_⟩
  intro L p t hL hp ht
  obtain ⟨a, q, hq, hqN, ha, hanum, happ⟩ := exists_approx_unit_interval_real t hL ht
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hqL : (q : ℝ) ≤ L := (Nat.cast_le.mpr hqN).trans (Nat.floor_le (by linarith))
  have hprofile := rpow_le_scaledArcProfile (weylSupremum L t) (C * L) L q
    |t - (a : ℝ) / q| p (weylSupremum_nonneg (by linarith) t) (by positivity)
    (by linarith) hq' (abs_nonneg _) hp (hb L t a q hL hq hqL ha happ)
  have hterm : (q : ℝ) ^ (-p / 2) * scaledArcProfile L (p / 2) ((a : ℝ) / q) t ≤
      rationalArcEnvelope L (p / 2) ⌊L⌋₊ t := by
    have hinner : scaledArcProfile L (p / 2) ((a : ℝ) / q) t ≤
        ∑ b ∈ Icc (-1 : ℤ) ((q : ℤ) + 1), scaledArcProfile L (p / 2) ((b : ℝ) / q) t :=
      single_le_sum (fun (b : ℤ) _ => scaledArcProfile_nonneg L (p / 2) ((b : ℝ) / q) t) hanum
    refine (mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hq'.le _)).trans ?_
    rw [show (-p / 2 : ℝ) = -(p / 2) by ring]
    unfold rationalArcEnvelope
    apply single_le_sum _ (mem_Icc.mpr ⟨hq, hqN⟩)
    intro k hk
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    apply sum_nonneg
    intro b hb
    exact scaledArcProfile_nonneg _ _ _ _

  rw [scaledArcProfile_eq] at hterm
  refine hprofile.trans ?_
  have hh := mul_le_mul_of_nonneg_left hterm (Real.rpow_nonneg (mul_nonneg hC.le (by linarith : 0 ≤ L)) p)
  exact (mul_assoc _ _ _).le.trans hh

end WaveTurbulence.WeylSums
