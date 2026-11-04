/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialEnergy
public import WaveTurbulence.Foundations.WKEL2.RadialWeightMeasure

/-!
# Radial Cauchy–Schwarz without assuming finite energy on every ray

Research-note Lemma 3 in nonnegative extended-integral form.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Cancellation of the positive weight in the Cauchy–Schwarz factors. -/
theorem ofReal_weighted_abs_cancel (w a r : ℝ) (hw : 0 < w) :
    (ENNReal.ofReal |w * a| * ENNReal.ofReal r) * ENNReal.ofReal (w⁻¹) =
      ENNReal.ofReal r * ENNReal.ofReal |a| := by
  rw [abs_mul, abs_of_pos hw, ENNReal.ofReal_mul hw.le]
  calc
    _ = (ENNReal.ofReal r * ENNReal.ofReal |a|) *
        (ENNReal.ofReal w * ENNReal.ofReal (w⁻¹)) := by ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul hw.le, mul_inv_cancel₀ hw.ne', ENNReal.ofReal_one, mul_one]

/-- Squared left Cauchy–Schwarz factor. -/
theorem ofReal_abs_mul_sq (a r : ℝ) (hr : 0 ≤ r) :
    (ENNReal.ofReal |a| * ENNReal.ofReal r) ^ 2 =
      ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (a ^ 2) := by
  rw [mul_pow, ← ENNReal.ofReal_pow (abs_nonneg a) 2, ← ENNReal.ofReal_pow hr 2, sq_abs]
  exact mul_comm _ _

/-- The inverse squared weight is the exact Japanese decay in A_k. -/
theorem inverse_weight_sq (s : ℝ) (x : Mom d) :
    (((1 + ‖x‖ ^ 2) ^ (s / 2))⁻¹) ^ 2 = japaneseDecay (2 * s) x := by
  rw [← Real.rpow_neg (by positivity), ← Real.rpow_mul_natCast (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [japaneseDecay]
  congr 1
  ring

/-- Extended radial Cauchy–Schwarz. Infinite exceptional ray energies remain explicit. -/
theorem radialMass_le_energy_weight (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {f : Mom d → ℝ} (hf : Measurable f)
    (k v : Mom d) (hv : ‖v‖ = 1) :
    radialMass f k v ≤ (radialEnergy s f k v) ^ ((1 : ℝ) / 2) *
      (ENNReal.ofReal (radialWeight d s k v)) ^ ((1 : ℝ) / 2) := by
  let L : Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal |weightedFunction s f (k + r.1 • v)| * ENNReal.ofReal r.1
  let R : Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (((1 + ‖k + r.1 • v‖ ^ 2) ^ (s / 2))⁻¹)
  have hRay : Continuous (fun r : Ioi (0 : ℝ) => k + r.1 • v) := by fun_prop
  have hL : Measurable L :=
    (((measurable_weightedFunction s hf).abs.ennreal_ofReal).comp hRay.measurable).mul
      measurable_subtype_coe.ennreal_ofReal
  have hbase : Continuous (fun r : Ioi (0 : ℝ) => 1 + ‖k + r.1 • v‖ ^ 2) := by fun_prop
  have hR : Measurable R :=
    (hbase.rpow_const (fun _ => Or.inl (by positivity))).measurable.inv.ennreal_ofReal
  have hMass : (∫⁻ r, (L * R) r ∂Measure.volumeIoiPow (d - 3)) = radialMass f k v := by
    calc
      _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal r.1 * ENNReal.ofReal |f (k + r.1 • v)|
          ∂Measure.volumeIoiPow (d - 3) := by
        apply lintegral_congr
        intro r
        exact ofReal_weighted_abs_cancel _ _ _ (Real.rpow_pos_of_pos (by positivity) _)
      _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal |f (k + r.1 • v)|
          ∂Measure.volumeIoiPow (d - 3 + 1) := by
        simpa only [pow_one, Function.comp_def] using lintegral_volumeIoiPow_pow (d - 3) 1
          ((hf.abs.ennreal_ofReal).comp hRay.measurable)
      _ = _ := by rw [show d - 3 + 1 = d - 2 by omega]; rfl
  have hEnergy : (∫⁻ r, L r ^ 2 ∂Measure.volumeIoiPow (d - 3)) = radialEnergy s f k v := by
    calc
      _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1 ^ 2) *
          ENNReal.ofReal ((weightedFunction s f (k + r.1 • v)) ^ 2)
          ∂Measure.volumeIoiPow (d - 3) := by
        apply lintegral_congr
        intro r
        exact ofReal_abs_mul_sq _ _ r.2.le
      _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal ((weightedFunction s f (k + r.1 • v)) ^ 2)
          ∂Measure.volumeIoiPow (d - 3 + 2) :=
        lintegral_volumeIoiPow_pow (d - 3) 2
          ((((measurable_weightedFunction s hf).pow_const 2).ennreal_ofReal).comp hRay.measurable)
      _ = _ := by rw [show d - 3 + 2 = d - 1 by omega]; rfl
  have hA : (∫⁻ r, R r ^ 2 ∂Measure.volumeIoiPow (d - 3)) =
      ENNReal.ofReal (radialWeight d s k v) := by
    calc
      _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (japaneseDecay (2 * s) (k + r.1 • v))
          ∂Measure.volumeIoiPow (d - 3) := by
        apply lintegral_congr
        intro r
        change (ENNReal.ofReal (((1 + ‖k + r.1 • v‖ ^ 2) ^ (s / 2))⁻¹)) ^ 2 = _
        rw [← ENNReal.ofReal_pow (by positivity) 2, inverse_weight_sq]
      _ = _ := lintegral_radialWeight_measure hd s hs k v hv
  have hconj : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.volumeIoiPow (d - 3)) hconj
    hL.aemeasurable hR.aemeasurable
  simp only [ENNReal.rpow_two] at h
  rw [hMass, hEnergy, hA] at h
  exact h

end WaveTurbulence.WKEL2
