/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.LocalArcCover
public import WaveTurbulence.Foundations.WeylSums.ArcIntegration

/-! # Integration of the localized rational cover -/

public section
open MeasureTheory Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Positive majorant retaining only the possible nonzero numerators. -/
@[expose] noncomputable def localArcEnvelope (L σ : ℝ) (N : ℕ) (T t : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 N, (q : ℝ) ^ (-σ) *
    ∑ a ∈ localNumerators T q, scaledArcProfile L σ ((a : ℝ) / q) t

theorem localArcEnvelope_nonneg (L σ : ℝ) (N : ℕ) (T t : ℝ) :
    0 ≤ localArcEnvelope L σ N T t := by
  apply sum_nonneg
  intro q hq
  apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  exact sum_nonneg (fun a _ => scaledArcProfile_nonneg _ _ _ _)

theorem integrable_localArcEnvelope {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (N : ℕ) (T : ℝ) :
    Integrable (localArcEnvelope L σ N T) := by
  apply integrable_finsetSum
  intro q _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro a _
  exact integrable_scaledArcProfile hL hσ _

/-- Exact integral of the finite rational cover. -/
theorem integral_localArcEnvelope {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (N : ℕ) (T : ℝ) :
    (∫ t : ℝ, localArcEnvelope L σ N T t) =
      arcProfileMass σ / L ^ 2 * ∑ q ∈ Icc 1 N, ((localNumerators T q).card : ℝ) * (q : ℝ) ^ (-σ) := by
  unfold localArcEnvelope
  have hint (q : ℕ) : Integrable (fun t : ℝ => (q : ℝ) ^ (-σ) *
      ∑ a ∈ localNumerators T q, scaledArcProfile L σ ((a : ℝ) / (q : ℝ)) t) :=
    (integrable_finsetSum (localNumerators T q)
      (fun a _ => integrable_scaledArcProfile hL hσ ((a : ℝ) / (q : ℝ)))).const_mul _
  rw [integral_finsetSum (Icc 1 N) (fun q _ => hint q)]
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  rw [integral_const_mul, integral_finsetSum (localNumerators T q)
    (fun a _ => integrable_scaledArcProfile hL hσ ((a : ℝ) / (q : ℝ)))]
  simp_rw [integral_scaledArcProfile hL]
  rw [sum_const, nsmul_eq_mul]
  ring

/-- The localized cover gains the length `T`, before denominator summation. -/
theorem integral_localArcEnvelope_le {L σ T : ℝ} (hL : 0 < L) (hσ : 1 < σ)
    (hT : 0 ≤ T) (N : ℕ) :
    (∫ t : ℝ, localArcEnvelope L σ N T t) ≤
      4 * (arcProfileMass σ / L ^ 2) * T * arcDenominatorSum σ N := by
  rw [integral_localArcEnvelope hL hσ N T]
  have hsum : (∑ q ∈ Icc 1 N, ((localNumerators T q).card : ℝ) * (q : ℝ) ^ (-σ)) ≤
      4 * T * arcDenominatorSum σ N := by
    rw [arcDenominatorSum, mul_sum]
    apply sum_le_sum
    intro q hq
    have hqp : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (mem_Icc.mp hq).1)
    calc
      _ ≤ (4 * (q : ℝ) * T) * (q : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (localNumerators_card_le hT q) (Real.rpow_nonneg hqp.le _)
      _ = 4 * T * (q : ℝ) ^ (1 - σ) := by
        rw [sub_eq_add_neg, Real.rpow_add hqp, Real.rpow_one]
        ring
  have hh := mul_le_mul_of_nonneg_left hsum
    (div_nonneg (arcProfileMass_nonneg σ) (sq_nonneg L))
  simpa only [mul_assoc, mul_left_comm] using hh

end WaveTurbulence.WeylSums
