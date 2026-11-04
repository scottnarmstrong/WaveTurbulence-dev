/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# The literal two-clock causal triangle

The non-reversed triangular time integral is exactly integration over the
three causal inequalities in the source tree time domain.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The root clock is below `t` and above the lone-parent clock, which is above `s`. -/
@[expose] def causalTriangle (t s : ℝ) : Set (Fin 2 → ℝ) :=
  {u | s ≤ u 1 ∧ u 1 ≤ u 0 ∧ u 0 ≤ t}

theorem measurableSet_causalTriangle (t s : ℝ) : MeasurableSet (causalTriangle t s) := by
  exact (measurableSet_le measurable_const (measurable_pi_apply 1)).inter
    ((measurableSet_le (measurable_pi_apply 1) (measurable_pi_apply 0)).inter
      (measurableSet_le (measurable_pi_apply 0) measurable_const))

/-- Fubini over the actual causal triangle, including its boundary conventions. -/
theorem integral_triangle_eq_setIntegral {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F)
    {s t : ℝ} (hst : s ≤ t) :
    (∫ x in s..t, ∫ y in s..x, F ![x, y]) = ∫ u in causalTriangle t s, F u := by
  let G : ℝ × ℝ → ℂ := fun z => F (MeasurableEquiv.finTwoArrow.symm z)
  let T : Set (ℝ × ℝ) := {z | s ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ t}
  have hT : MeasurableSet T := by
    exact ((measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)))
  have hG : Integrable G :=
    ((volume_preserving_finTwoArrow ℝ).symm.integrable_comp_emb
      MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).mpr hF
  have hp := integral_prod (T.indicator G) (hG.indicator hT)
  rw [integral_indicator hT] at hp
  have hi (x : ℝ) : (∫ y, T.indicator G (x, y)) =
      (Icc s t).indicator (fun x => ∫ y in Icc s x, G (x, y)) x := by
    by_cases hx : x ∈ Icc s t
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        by_cases hy : y ∈ Icc s x
        · simp [T, hx.2, hy.1, hy.2]
        · have hn : ¬ (s ≤ y ∧ y ≤ x ∧ x ≤ t) := fun h => hy ⟨h.1, h.2.1⟩
          simp [T, hn, hy])
    · rw [indicator_of_notMem hx]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall (fun y => by
        have hn : ¬ (s ≤ y ∧ y ≤ x ∧ x ≤ t) := fun h => hx ⟨h.1.trans h.2.1, h.2.2⟩
        simp [T, hn])
  simp_rw [hi] at hp
  rw [integral_indicator measurableSet_Icc] at hp
  change (∫ z in T, G z) = (∫ x in Icc s t, ∫ y in Icc s x, G (x, y)) at hp
  have htransport := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding G T
  have hpre : MeasurableEquiv.finTwoArrow ⁻¹' T = causalTriangle t s := rfl
  rw [hpre] at htransport
  have he (u : Fin 2 → ℝ) : G (MeasurableEquiv.finTwoArrow u) = F u := by
    exact congrArg F (MeasurableEquiv.symm_apply_apply _ _)
  simp_rw [he] at htransport
  rw [htransport, hp, intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]
  rfl

end WaveTurbulence.Incoh
