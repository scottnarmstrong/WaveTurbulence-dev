/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremumArcs
public import WaveTurbulence.Foundations.WeylSums.LocalArcIntegration

/-! # A localized envelope for the supremum Weyl sum -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- The same uniform Gauss bound, restricted to nonzero numerator arcs. -/
theorem exists_weylSupremum_local_arc_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L p T t : ℝ), 2 ≤ L → 0 ≤ p →
      1 / L < |t| → |t| ≤ T →
      weylSupremum L t ^ p ≤ (C * L) ^ p * localArcEnvelope L (p / 2) ⌊L⌋₊ T t := by
  obtain ⟨C, hC, hb⟩ := exists_weylSupremum_bound
  refine ⟨C, hC, ?_⟩
  intro L p T t hL hp ht htT
  obtain ⟨a, q, hq, hqN, ha, hanum, happ⟩ := exists_approx_local hL ht htT
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hqL : (q : ℝ) ≤ L := (Nat.cast_le.mpr hqN).trans (Nat.floor_le (by linarith))
  have hprofile := rpow_le_scaledArcProfile (weylSupremum L t) (C * L) L q
    |t - (a : ℝ) / q| p (weylSupremum_nonneg (by linarith) t) (by positivity)
    (by linarith) hq' (abs_nonneg _) hp (hb L t a q (by linarith) hq hqL ha happ)
  have hterm : (q : ℝ) ^ (-p / 2) * scaledArcProfile L (p / 2) ((a : ℝ) / q) t ≤
      localArcEnvelope L (p / 2) ⌊L⌋₊ T t := by
    have hinner : scaledArcProfile L (p / 2) ((a : ℝ) / q) t ≤
        ∑ b ∈ localNumerators T q, scaledArcProfile L (p / 2) ((b : ℝ) / q) t :=
      single_le_sum (fun (b : ℤ) _ => scaledArcProfile_nonneg L (p / 2) ((b : ℝ) / q) t) hanum
    refine (mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hq'.le _)).trans ?_
    rw [show (-p / 2 : ℝ) = -(p / 2) by ring]
    unfold localArcEnvelope
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
