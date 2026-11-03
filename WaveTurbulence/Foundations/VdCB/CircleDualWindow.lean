/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualEndpointASum
public import WaveTurbulence.Foundations.VdCB.StationaryFrequencyImage

/-!
# The actual open circle dual window at the transformed scale

The numeric source-frequency comparisons control the actual first and
last integer frequencies. They place the full window, with its possible
last endpoint, inside the proved weighted A-process range.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The weighted actual circle dual sum has the B-after-A³ scale on any
open integer window satisfying the literal source-frequency comparisons. -/
theorem norm_sum_circleDualWindow_le {R h U A B : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hU : 1 ≤ U) (p q : ℝ)
    (hfrequency : ∀ k ∈ openFrequencies A B,
      h ≤ (k : ℝ) ∧ R * h ^ 2 / (9 * U) ≤ (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ R * h ^ 2 / U) :
    ‖∑ k ∈ openFrequencies A B, (circleDualWeight R h k : ℂ) *
      expPhase (circleLatticeDualPhase R h k + p * (k : ℝ) + q)‖ ≤
        154618822665 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  let a : ℤ := ⌊A⌋
  let K : ℕ := (⌈B⌉ - 1 - ⌊A⌋).toNat
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hset : openFrequencies A B = Finset.Ioc a (a + K) := openFrequencies_eq_Ioc A B
  have hsum : (∑ k ∈ openFrequencies A B, (circleDualWeight R h k : ℂ) *
      expPhase (circleLatticeDualPhase R h k + p * (k : ℝ) + q)) =
      ∑ j ∈ Finset.range K, (circleDualWeight R h ((a + j + 1 : ℤ) : ℝ) : ℂ) *
        expPhase (circleLatticeDualPhase R h ((a + j + 1 : ℤ) : ℝ) + p * ((a + j + 1 : ℤ) : ℝ) + q) :=
    sum_openFrequencies_eq_range (fun k : ℤ => (circleDualWeight R h k : ℂ) *
      expPhase (circleLatticeDualPhase R h k + p * (k : ℝ) + q)) A B
  by_cases hK : K = 0
  · rw [hsum, hK, Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
  have hfirst : a + 1 ∈ openFrequencies A B := by
    rw [hset]
    apply Finset.mem_Ioc.mpr
    omega
  have hlast : a + K ∈ openFrequencies A B := by
    rw [hset]
    apply Finset.mem_Ioc.mpr
    omega
  obtain ⟨hfirsth, hfirstlo, hfirsthi⟩ := hfrequency (a + 1) hfirst
  obtain ⟨hlasth, _, hlasthi⟩ := hfrequency (a + K) hlast
  simp only [Int.cast_add, Int.cast_one] at hfirsth hfirstlo hfirsthi
  simp only [Int.cast_add, Int.cast_natCast] at hlasth hlasthi
  have hYp : 0 < (a : ℝ) + 1 := hh.trans_le hfirsth
  have hYint : (0 : ℤ) < a + 1 := by exact_mod_cast hYp
  have hY : (1 : ℝ) ≤ (a : ℝ) + 1 := by
    have hh : (1 : ℤ) ≤ a + 1 := by omega
    exact_mod_cast hh
  have hA0 : 0 ≤ R * h ^ 2 := by positivity
  have hRY : ((a : ℝ) + 1) ^ 2 ≤ R * h ^ 2 := hfirsthi.trans (div_le_self hA0 hU)
  have hlastsq : ((a : ℝ) + K) ^ 2 ≤ 9 * ((a : ℝ) + 1) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hfirstlo (by norm_num : (0 : ℝ) ≤ 9)
    have heq : 9 * (R * h ^ 2 / (9 * U)) = R * h ^ 2 / U := by ring
    rw [heq] at hh
    exact hlasthi.trans hh
  have hlastp : 0 < (a : ℝ) + K := hh.trans_le hlasth
  have hlast3 : (a : ℝ) + K ≤ 3 * ((a : ℝ) + 1) := by nlinarith only [hlastsq, hlastp, hYp]
  have hKbound : (K : ℝ) ≤ 2 * ((a : ℝ) + 1) + 1 := by linarith only [hlast3]
  have he := norm_sum_circleDualWeight_mul_le_B_scale_succ a K p q hR hh hU0 hY hfirsth hRY hKbound hfirstlo
  rw [hsum]
  convert he using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [show (a : ℝ) + (j : ℝ) + 1 = (a : ℝ) + 1 + j by ring]

end WaveTurbulence.VdCB
