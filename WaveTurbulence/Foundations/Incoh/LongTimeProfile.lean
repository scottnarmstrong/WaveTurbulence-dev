/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LongTime

/-!
# Nonnegative long-frequency profiles

TARGET (incohproof13): the landed long-frequency integral bound is
transported to the nonnegative profile consumed by the time-box Tonelli bound.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal masked link restricted to the long-frequency window. -/
@[expose] def longLinkProfile {d : ℕ} (L R : ℝ) (A : LinkParameters d) (s : ℝ) : ℝ≥0∞ :=
  (longTimeWindow L R).indicator (fun s => ‖linkLatticeSum L s A‖ₑ) s

theorem measurable_longLinkProfile {d : ℕ} {L : ℝ} (hL : 0 < L) (R : ℝ)
    (A : LinkParameters d) : Measurable (longLinkProfile L R A) :=
  (continuous_linkLatticeSum hL A).measurable.enorm.indicator (measurableSet_longTimeWindow L R)

/-- The real-valued integral and nonnegative profile mass agree, with genuine integrability. -/
theorem lintegral_longLinkProfile_eq {d : ℕ} {L : ℝ} (hL : 0 < L) (R : ℝ)
    (A : LinkParameters d) :
    (∫⁻ s, longLinkProfile L R A s) =
      ENNReal.ofReal (∫ s in longTimeWindow L R, ‖linkLatticeSum L s A‖) := by
  have hi : IntegrableOn (fun s => ‖linkLatticeSum L s A‖) (longTimeWindow L R) :=
    ((continuous_linkLatticeSum hL A).norm.integrableOn_Icc).mono_set (longTimeWindow_subset L R)
  change (∫⁻ s, (longTimeWindow L R).indicator (fun s => ‖linkLatticeSum L s A‖ₑ) s) = _
  rw [lintegral_indicator (measurableSet_longTimeWindow L R)]
  simp_rw [← ofReal_norm]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm

/-- Uniform mass bound for the literal long-frequency profile. -/
theorem exists_longLinkProfile_mass_bound (d : ℕ) (hd : 3 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (T : ℝ) (hT : 0 < T) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ A : LinkParameters d,
      (∫⁻ s, longLinkProfile L (T * L ^ (2 * γ)) A s) ≤
        ENNReal.ofReal (C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)) := by
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := exists_longTime_link_integral_bound d hd γ hγ η hη T hT
  refine ⟨C, L₀, hC, hL₀, ?_⟩
  intro L hL A
  rw [lintegral_longLinkProfile_eq (zero_lt_one.trans_le (hL₀.trans hL))]
  exact ENNReal.ofReal_le_ofReal (hb L hL A)

end WaveTurbulence.Incoh
