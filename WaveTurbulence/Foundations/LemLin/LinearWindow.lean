/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarFlow
public import WaveTurbulence.Foundations.LemLin.TensorFactorization
public import WaveTurbulence.Foundations.LemLin.TrivialWindow
public import WaveTurbulence.Foundations.LemLin.LargestCoordinate

/-!
# Linear cancellation on short windows

TARGET `lemlin`, before specializing the window length. The vector frequency
need not be a lattice point: only its nonvanishing and the short-window
condition enter the proof.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set
open scoped Classical

/-- A constant depending only on dimension and the fixed cutoff. -/
@[expose] noncomputable def linearCancellationConstant (d : ℕ) : ℝ :=
  (3 : ℝ) ^ (d - 1) * d * scalarFourierMass

theorem linearCancellationConstant_nonneg (d : ℕ) : 0 ≤ linearCancellationConstant d := by
  unfold linearCancellationConstant
  exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) scalarFourierMass_nonneg

/-- TARGET `lemlin`, cancellation branch on an arbitrary short window. -/
theorem integral_linear_flow_cancellation {d : ℕ} {L T : ℝ}
    (hL : 1 ≤ L) (hT : 0 ≤ T) (a r ξ : Mom d) (hr : r ≠ 0)
    (hshort : T * ‖r‖ ≤ L) (τ : ℝ) :
    (∫ s in Icc τ (τ + T), ‖linearLatticeSum L a (s • r + ξ)‖) ≤
      linearCancellationConstant d * L ^ d / ‖r‖ := by
  have hLpos : 0 < L := by linarith
  have hmass := scalarFourierMass_nonneg
  obtain ⟨i, hi, hri⟩ := exists_large_coordinate r hr
  have hcoord : |r i| ≤ ‖r‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le r i
  have hshorti : |r i| * T ≤ L := by nlinarith
  have hs := integral_scalar_flow hLpos hT (neg_ne_zero.mpr (abs_pos.mp hi))
    (by simpa only [abs_neg] using hshorti) (a i) (-ξ i) τ
  have hscalar : Continuous (fun s : ℝ => ‖scalarLatticeSum L (a i) (-r i * s + -ξ i)‖) := by
    apply Continuous.norm
    apply (continuous_scalarLatticeSum hLpos (a i)).comp
    exact (continuous_const.mul continuous_id).add continuous_const
  have hdom :
      (∫ s in Icc τ (τ + T), ‖linearLatticeSum L a (s • r + ξ)‖) ≤
        (3 * L) ^ (d - 1) *
          (∫ s in Icc τ (τ + T), ‖scalarLatticeSum L (a i) (-r i * s + -ξ i)‖) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      (continuous_norm_linear_flow hLpos a r ξ).integrableOn_Icc
      (hscalar.const_mul _).integrableOn_Icc
      measurableSet_Icc
    intro s _
    have hb := norm_linearLatticeSum_le_coordinate hL a (s • r + ξ) i
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_add, neg_mul,
      mul_comm s] using hb
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hpow : (3 * L) ^ (d - 1) * L = (3 : ℝ) ^ (d - 1) * L ^ d := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]
  have hpos : 0 < ‖r‖ := norm_pos_iff.mpr hr
  calc
    _ ≤ (3 * L) ^ (d - 1) * (L * scalarFourierMass / |r i|) :=
      hdom.trans (mul_le_mul_of_nonneg_left (by simpa only [abs_neg] using hs) (by positivity))
    _ = ((3 : ℝ) ^ (d - 1) * L ^ d * scalarFourierMass) / |r i| := by
      rw [← mul_div_assoc]
      congr 1
      rw [← mul_assoc, hpow]
    _ ≤ linearCancellationConstant d * L ^ d / ‖r‖ := by
      apply (div_le_div_iff₀ hi hpos).mpr
      have hb := mul_le_mul_of_nonneg_left hri
        (show 0 ≤ (3 : ℝ) ^ (d - 1) * L ^ d * scalarFourierMass by positivity)
      dsimp [linearCancellationConstant]
      nlinarith only [hb]

end WaveTurbulence.LemLin
