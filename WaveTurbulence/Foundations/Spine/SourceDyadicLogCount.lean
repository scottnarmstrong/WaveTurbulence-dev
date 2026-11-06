/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDyadicCardinality
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Int.Interval
/-! Source dyadic choices have logarithmic cardinality, with explicit endpoint control. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- An interval of positive dyadic scales costs at most its base-two logarithmic length
plus one. Empty intervals of exponents are handled without an existence premise. -/
theorem card_sourceDyadicScales_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Nat.card {P : ℝ // SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P ≤ b} : ℝ) ≤
      Real.logb 2 b - Real.logb 2 a + 1 := by
  have hb : 0 < b := ha.trans_le hab
  rw [card_sourceDyadicScales ha hb]
  have hlo : Real.logb 2 a ≤ (Int.clog 2 a : ℝ) := by
    rw [← Real.ceil_logb_natCast ha.le]
    exact Int.le_ceil _
  have hhi : (Int.log 2 b : ℝ) ≤ Real.logb 2 b := by
    rw [← Real.floor_logb_natCast hb.le]
    exact Int.floor_le _
  by_cases h : Int.clog 2 a ≤ Int.log 2 b + 1
  · have he := Int.card_Icc_of_le (Int.clog 2 a) (Int.log 2 b) h
    have he' : ((Finset.Icc (Int.clog 2 a) (Int.log 2 b)).card : ℝ) =
        (Int.log 2 b : ℝ) + 1 - (Int.clog 2 a : ℝ) := by exact_mod_cast he
    rw [he']
    linarith
  · have hempty : Finset.Icc (Int.clog 2 a) (Int.log 2 b) = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hm : Real.logb 2 a ≤ Real.logb 2 b :=
      (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).monotoneOn ha hb hab
    linarith

/-- All positive ladder scales lie in this one logarithmic-size carrier. -/
theorem card_sourceLadderScales_le {L : ℝ} (hL : 1 ≤ L) :
    (Nat.card {P : ℝ // SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ 1} : ℝ) ≤
      Real.log L / Real.log 2 + 1 := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h := card_sourceDyadicScales_le (inv_pos.mpr hL0)
    (inv_le_one_of_one_le₀ hL)
  rw [Real.logb_one, Real.logb_inv] at h
  simpa only [zero_sub, neg_neg, Real.logb] using h

end WaveTurbulence.LGSpine
