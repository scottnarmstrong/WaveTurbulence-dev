/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.WickCorrection
public import WaveTurbulence.Foundations.Incoh.LongTimeExponents
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum2

/-!
# Long-frequency control for the masked link

TARGET (incohproof13), before the time-difference change of variables.
Lemma 5.3 is used as landed; the two Wick axes are estimated separately.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The source's long-frequency window. -/
@[expose] def longTimeWindow (L R : ℝ) : Set ℝ := {s | L ≤ |s| ∧ |s| ≤ R}

theorem measurableSet_longTimeWindow (L R : ℝ) : MeasurableSet (longTimeWindow L R) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

theorem longTimeWindow_subset (L R : ℝ) : longTimeWindow L R ⊆ Icc (-R) R :=
  fun _ hs => abs_le.mp hs.2

/-- The integrated Wick correction is bounded by its pointwise mass times the window length. -/
theorem integral_longTime_link_le {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (R : ℝ) (hR : 0 ≤ R)
    (A : LinkParameters d) :
    (∫ s in longTimeWindow L R, ‖linkLatticeSum L s A‖) ≤
      (∫ s in longTimeWindow L R,
        ‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖) +
      (2 * R) * (2 * (5 * L) ^ d) := by
  have hLp := zero_lt_one.trans_le hL
  let f := fun s => WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift
  have hf : IntegrableOn (fun s => ‖f s‖) (longTimeWindow L R) :=
    ((WeylSums.continuous_bilinearLatticeSum hLp _ _ _ _).norm.integrableOn_Icc).mono_set
      (longTimeWindow_subset L R)
  have hg : IntegrableOn (fun s => ‖linkLatticeSum L s A‖) (longTimeWindow L R) :=
    ((continuous_linkLatticeSum hLp A).norm.integrableOn_Icc).mono_set (longTimeWindow_subset L R)
  have hcbox : IntegrableOn (fun _ : ℝ => 2 * (5 * L) ^ d) (Icc (-R) R) :=
    continuous_const.integrableOn_Icc
  have hc := hcbox.mono_set (longTimeWindow_subset L R)
  have hbound : ∀ s : ℝ, ‖linkLatticeSum L s A‖ ≤ ‖f s‖ + 2 * (5 * L) ^ d := by
    intro s
    have htriangle := norm_add_le (f s) (linkLatticeSum L s A - f s)
    rw [add_sub_cancel] at htriangle
    exact htriangle.trans (add_le_add le_rfl (norm_linkLatticeSum_sub_bilinear_le hL s A))
  calc
    _ ≤ ∫ s in longTimeWindow L R, (‖f s‖ + 2 * (5 * L) ^ d) :=
      setIntegral_mono hg (hf.add hc) hbound
    _ = (∫ s in longTimeWindow L R, ‖f s‖) + ∫ _s in longTimeWindow L R, 2 * (5 * L) ^ d :=
      integral_add hf hc
    _ ≤ (∫ s in longTimeWindow L R, ‖f s‖) + ∫ _s in Icc (-R) R, 2 * (5 * L) ^ d :=
      add_le_add le_rfl (setIntegral_mono_set hcbox (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall (longTimeWindow_subset L R)))
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith : 0 ≤ R - -R)]
      congr 1
      ring

/-- TARGET (incohproof13) in the frequency variable, with constants before all centers and shifts. -/
theorem exists_longTime_link_integral_bound (d : ℕ) (hd : 3 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (T : ℝ) (hT : 0 < T) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ A : LinkParameters d,
      (∫ s in longTimeWindow L (T * L ^ (2 * γ)), ‖linkLatticeSum L s A‖) ≤
        C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) := by
  obtain ⟨C, L₀, hb⟩ := WeylSums.quadExpSum2_bound d hd γ hγ η hη T hT
  let E : ℝ := 2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ)
  let B : ℝ := 4 * 5 ^ d * T * T ^ ((d : ℝ) - 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨max C 1 + B, max L₀ 1, by positivity, le_max_right _ _, ?_⟩
  intro L hL A
  have hL₁ : 1 ≤ L := (le_max_right L₀ 1).trans hL
  have hLp := zero_lt_one.trans_le hL₁
  have hR : 0 < T * L ^ (2 * γ) := by positivity
  by_cases he : (longTimeWindow L (T * L ^ (2 * γ))).Nonempty
  · obtain ⟨s, hs⟩ := he
    have hwindow : L ≤ T * L ^ (2 * γ) := hs.1.trans hs.2
    have hbudget := axis_longTime_power_le (show 2 ≤ d by omega) hLp hT.le hwindow
    have herr : (2 * (T * L ^ (2 * γ))) * (2 * (5 * L) ^ d) ≤ B * L ^ (E + η) := by
      calc
        _ = (4 * 5 ^ d * T) * L ^ ((d : ℝ) + 2 * γ) := by
          rw [Real.rpow_add hLp, Real.rpow_natCast, mul_pow]
          ring
        _ ≤ (4 * 5 ^ d * T) * (T ^ ((d : ℝ) - 2) * L ^ E) :=
          mul_le_mul_of_nonneg_left hbudget (by positivity)
        _ = B * L ^ E := by dsimp [B]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL₁ (by linarith : E ≤ E + η)) hB
    have hpure := hb L ((le_max_left L₀ 1).trans hL)
      A.leftCenter A.rightCenter A.leftShift A.rightShift
    calc
      _ ≤ (∫ s in longTimeWindow L (T * L ^ (2 * γ)),
          ‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖) +
            (2 * (T * L ^ (2 * γ))) * (2 * (5 * L) ^ d) :=
        integral_longTime_link_le hL₁ _ hR.le A
      _ ≤ C * L ^ (E + η) + B * L ^ (E + η) := add_le_add hpure herr
      _ ≤ max C 1 * L ^ (E + η) + B * L ^ (E + η) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)) le_rfl
      _ = _ := by ring
  · rw [Set.not_nonempty_iff_eq_empty.mp he, setIntegral_empty]
    positivity

end WaveTurbulence.Incoh
