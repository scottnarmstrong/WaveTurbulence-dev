/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LongTimeProfile
public import WaveTurbulence.Foundations.Incoh.LayerBoxProfile

/-!
# Long-time bounds on the literal link boxes

TARGET (incohproof13). The long-frequency estimate is uniform in the
localization data, and the box change of variables contributes precisely
one inverse time-frequency scale.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof13), before substituting the kinetic frequency scale. -/
theorem exists_longTime_box_bounds (d : ℕ) (hd : 3 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (T : ℝ) (hT : 0 < T) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ lam : ℝ, 0 < lam → ∀ Q : LayerLink d,
      (∫⁻ t in linkBox Q, longLinkProfile L (T * L ^ (2 * γ)) Q.toLinkParameters
        (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1))) ≤
      ENNReal.ofReal lam⁻¹ *
        ENNReal.ofReal (C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)) := by
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := exists_longLinkProfile_mass_bound d hd γ hγ η hη T hT
  refine ⟨C, L₀, hC, hL₀, ?_⟩
  intro L hL lam hlam Q
  have hLp : 0 < L := zero_lt_one.trans_le (hL₀.trans hL)
  exact (lintegral_layerBox_profile_le Q hlam
    (measurable_longLinkProfile hLp _ Q.toLinkParameters)).trans
      (mul_le_mul' le_rfl (hb L hL Q.toLinkParameters))

end WaveTurbulence.Incoh
