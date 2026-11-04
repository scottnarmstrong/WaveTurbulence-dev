/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ShortTimeBox
public import WaveTurbulence.Foundations.Incoh.LongTimeBox

/-!
# Splitting a literal link into its short and long frequencies

TARGET (incohproof13)–(incohproof16). A structural bound on the two
integer layers supplies the frequency window; it is not an analytic estimate.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual absolute link mass, with its time-frequency scale separated from the coupling. -/
@[expose] def layerLinkMass {d : ℕ} (L lam : ℝ) (Q : LayerLink d) : ℝ≥0∞ :=
  ∫⁻ t in linkBox Q,
    ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)) Q.toLinkParameters‖ₑ

/-- The two profile windows cover every frequency up to the structural maximal frequency. -/
theorem enorm_link_le_short_add_long {d : ℕ} (L R s : ℝ) (A : LinkParameters d)
    (hs : |s| ≤ R) :
    ‖linkLatticeSum L s A‖ₑ ≤ shortLinkProfile L A s + longLinkProfile L R A s := by
  by_cases hshort : |s| ≤ L
  · have hmem : s ∈ Icc (-L) L := abs_le.mp hshort
    rw [shortLinkProfile, Set.indicator_of_mem (s := Icc (-L) L) hmem]
    exact le_add_right le_rfl
  · have hmem : s ∈ longTimeWindow L R := ⟨(lt_of_not_ge hshort).le, hs⟩
    rw [longLinkProfile, Set.indicator_of_mem (s := longTimeWindow L R) hmem]
    exact le_add_left le_rfl

/-- A bound on the layer span gives the literal maximal oscillatory frequency. -/
theorem abs_layerFrequency_le {d : ℕ} (Q : LayerLink d) {lam D : ℝ} (hlam : 0 ≤ lam)
    (hspan : |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D)
    {t : Fin 2 → ℝ} (ht : t ∈ linkBox Q) :
    |((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)| ≤ D * lam := by
  have hu : |((Q.orientation : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or Q.orientation with h | h <;> simp only [h] <;> norm_num
  rw [abs_mul, abs_mul, hu, one_mul, abs_of_nonneg hlam]
  exact (mul_le_mul_of_nonneg_left ((abs_timeDifference_le Q ht).trans hspan) hlam).trans_eq (mul_comm _ _)

/-- Full absolute mass is bounded by the two proved frequency pieces on the same literal box. -/
theorem layerLinkMass_le_short_add_long {d : ℕ} {L lam D : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (Q : LayerLink d)
    (hspan : |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D) :
    layerLinkMass L lam Q ≤
      (∫⁻ t in linkBox Q, shortLinkTimeProfile L lam Q t) +
      ∫⁻ t in linkBox Q, longLinkProfile L (D * lam) Q.toLinkParameters
        (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)) := by
  have hphase : Measurable (fun t : Fin 2 → ℝ =>
      ((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)) := by fun_prop
  have hshort : Measurable (shortLinkTimeProfile L lam Q) :=
    (measurable_shortLinkProfile hL Q.toLinkParameters).comp hphase
  calc
    _ ≤ ∫⁻ t in linkBox Q, (shortLinkTimeProfile L lam Q t +
        longLinkProfile L (D * lam) Q.toLinkParameters
          (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1))) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact enorm_link_le_short_add_long _ _ _ _ (abs_layerFrequency_le Q hlam hspan ht)
    _ = _ := lintegral_add_left hshort _

end WaveTurbulence.Incoh
