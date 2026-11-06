/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AlphaInt
public import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic
/-! `sup_β ∫_S ⟨a+β⟩⁻¹ da ≲ log |S|` (TARGET L2018, the elementary inequality of Step 3). -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Ladder

theorem integral_br_inv {M : ℝ} :
    ∫ x in (-M)..M, (br x)⁻¹ = 2 * Real.arsinh M := by
  have hd : ∀ x ∈ uIcc (-M) M, HasDerivAt Real.arsinh (br x)⁻¹ x := fun x _ => by
    simpa [br] using Real.hasDerivAt_arsinh x
  have hc : IntervalIntegrable (fun x => (br x)⁻¹) volume (-M) M :=
    (continuous_br.inv₀ (fun x => (br_pos x).ne')).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc, Real.arsinh_neg]; ring

theorem lintegral_br_inv_le {S : Set ℝ} (hS : MeasurableSet S) {M : ℝ} (hM : 1 ≤ M)
    (hvol : volume S ≤ ENNReal.ofReal M) (β : ℝ) :
    ∫⁻ a in S, ENNReal.ofReal (br (a + β))⁻¹ ≤ ENNReal.ofReal (2 * Real.arsinh M + 1) := by
  set g1 : ℝ → ℝ≥0∞ := (Icc (-M - β) (M - β)).indicator (fun a => ENNReal.ofReal (br (a + β))⁻¹)
    with hg1
  have hpt : ∀ a, ENNReal.ofReal (br (a + β))⁻¹ ≤ g1 a + ENNReal.ofReal M⁻¹ := by
    intro a
    by_cases h : a ∈ Icc (-M - β) (M - β)
    · rw [hg1]; simp only [Set.indicator_of_mem h]; exact le_self_add
    · rw [hg1]; simp only [Set.indicator_of_notMem h, zero_add]
      apply ENNReal.ofReal_le_ofReal
      have : M < |a + β| := by
        rw [mem_Icc] at h; push Not at h
        by_cases h1 : -M - β ≤ a
        · have := h h1; linarith [le_abs_self (a + β)]
        · push Not at h1; have : a + β < -M := by linarith
          linarith [neg_abs_le (a + β)]
      have hb : |a + β| ≤ br (a + β) := by
        unfold br; rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (a + β)])
      exact inv_anti₀ (by linarith) (by linarith)
  calc ∫⁻ a in S, ENNReal.ofReal (br (a + β))⁻¹ ≤ ∫⁻ a in S, (g1 a + ENNReal.ofReal M⁻¹) :=
        lintegral_mono hpt
    _ = (∫⁻ a in S, g1 a) + ENNReal.ofReal M⁻¹ * volume S := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ (∫⁻ a, g1 a) + ENNReal.ofReal M⁻¹ * ENNReal.ofReal M :=
        add_le_add (setLIntegral_le_lintegral _ _) (by gcongr)
    _ ≤ ENNReal.ofReal (2 * Real.arsinh M) + 1 := by
        refine add_le_add ?_ ?_
        · rw [hg1, lintegral_indicator measurableSet_Icc]
          have hint : IntegrableOn (fun a : ℝ => (br (a + β))⁻¹) (Icc (-M - β) (M - β)) :=
            (Continuous.integrableOn_Icc (by
              exact (continuous_br.comp (continuous_id.add continuous_const)).inv₀
                (fun x => (br_pos _).ne')))
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun a => (inv_pos.mpr (br_pos _)).le))]
          apply ENNReal.ofReal_le_ofReal
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
          have := integral_br_inv (M := M)
          refine le_of_eq ?_
          calc ∫ a in (-M - β)..(M - β), (br (a + β))⁻¹ = ∫ x in (-M)..M, (br x)⁻¹ := by
                rw [intervalIntegral.integral_comp_add_right (fun x => (br x)⁻¹) β]
                congr 1 <;> ring
            _ = _ := this
        · rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by linarith)]; simp
    _ = ENNReal.ofReal (2 * Real.arsinh M + 1) := by
        rw [ENNReal.ofReal_add (by positivity [Real.arsinh_nonneg_iff.mpr (by linarith : 0 ≤ M)]) (by norm_num)]
        simp

end WaveTurbulence.Ladder
