/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.Dirichlet
public import WaveTurbulence.Foundations.WeylSums.ArcProfile
import Mathlib.Tactic

/-!
# Rational covers of a unit interval

Dirichlet approximation selects one term of a finite positive major-arc
envelope. Integrating this envelope separates arc mass from denominator
counting. The slight enlargement `-1 ≤ a ≤ q+1` avoids endpoint conventions.
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- Dirichlet approximation on a unit interval with an explicit finite range
of numerators. The range is intentionally enlarged at both endpoints. -/
theorem exists_approx_unit_interval (t : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ N ∧ a.natAbs.Coprime q ∧
      a ∈ Icc (-1 : ℤ) ((q : ℤ) + 1) ∧ |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * N) := by
  obtain ⟨a, q, hq, hqN, ha, happ⟩ := exists_coprime_approx t hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hN' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hden : (q : ℝ) ≤ q * N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN' hq'.le
  have herr : |t - (a : ℝ) / q| ≤ 1 / (q : ℝ) :=
    happ.trans (one_div_le_one_div_of_le hq' hden)
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  have hl' := mul_le_mul_of_nonneg_right hl hq'.le
  have hu' := mul_le_mul_of_nonneg_right hu hq'.le
  have hmul : (t - (a : ℝ) / q) * q = t * q - a := by field_simp
  rw [hmul, neg_mul, div_mul_cancel₀ _ hq'.ne'] at hl'
  rw [hmul, div_mul_cancel₀ _ hq'.ne'] at hu'
  have htq0 : 0 ≤ t * q := mul_nonneg ht.1 hq'.le
  have htq1 : t * q ≤ q := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hq'.le
  have hal : (-1 : ℝ) ≤ a := by linarith only [hu', htq0]
  have hau : (a : ℝ) ≤ q + 1 := by linarith only [hl', htq1]
  refine ⟨a, q, hq, hqN, ha, mem_Icc.mpr ⟨?_, ?_⟩, happ⟩
  · exact_mod_cast hal
  · exact_mod_cast hau

/-- Positive envelope formed from all candidate rational arcs. -/
@[expose] noncomputable def rationalArcEnvelope (L σ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 N, (q : ℝ) ^ (-σ) *
    ∑ a ∈ Icc (-1 : ℤ) ((q : ℤ) + 1), scaledArcProfile L σ ((a : ℝ) / q) t

theorem rationalArcEnvelope_nonneg (L σ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ rationalArcEnvelope L σ N t := by
  apply sum_nonneg
  intro q _
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sum_nonneg (fun a _ => scaledArcProfile_nonneg _ _ _ _))

theorem numerator_range_card (q : ℕ) : (Icc (-1 : ℤ) ((q : ℤ) + 1)).card = q + 3 := by
  rw [Int.card_Icc]
  omega

end WaveTurbulence.WeylSums
