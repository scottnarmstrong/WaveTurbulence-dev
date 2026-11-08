/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.KinkSynth
public import WaveTurbulence.Foundations.Sumint.CountableExtensionMinkowski

/-! # PROT-PIN (D3-KINK): the zero-extended terminal operator at a fixed lower endpoint (target (2))

`termKink_sum`: for a countable family with absolutely summable coefficients, the terminal operator
`T ↦ Σ_i c_i ∫_{(s,T)} e^{πiA_i(u-s)} h_i(T,u) du` (zero for `T ≤ s`, kinked at `T = s`; o73 (13.1)–(13.2) with the
pin above the clock) agrees on the window `|T - s| ≤ 1` with `g = Σ_i c_i Gsyn_i`, and
`‖g‖_{A^θ} ≤ 2^θ Bk Σ_i |c_i| ‖h_i‖_{A^θ}` for `0 ≤ θ ≤ 1/2` (`Bk`: the uniform kinked-atom bound).
The sum is a counting integral (main's `count_integral_eq_tsum`, `integrable_count_prod_of_sum_mass`), whose norm is
bounded by Minkowski (`timeFourierNorm_count_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

/-- Minkowski for a countable sum, as a counting integral. -/
theorem timeFourierNorm_count_le {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {r : ℕ} (θ : ℝ) (F : ι → (Fin r → ℝ) → ℂ) (hFm : ∀ j, Measurable (F j)) (hFi : ∀ j, Integrable (F j))
    (hF : (∑' j, ∫⁻ t, ‖F j t‖ₑ) < ⊤) :
    timeFourierNorm θ (fun t => ∫ j, F j t ∂Measure.count) ≤ ∑' j, timeFourierNorm θ (F j) := by
  have hm : Measurable (fun p : ι × (Fin r → ℝ) => F p.1 p.2) :=
    measurable_from_prod_countable_right (f := fun p : ι × (Fin r → ℝ) => F p.1 p.2) (fun j => hFm j)
  refine (timeFourierNorm_integral_le (μ := Measure.count) θ F hm
    (Sumint.integrable_count_prod_of_sum_mass F hFm hF) hFi).trans_eq ?_
  exact lintegral_count _

open WaveTurbulence.Fourier in
/-- **(2)** The terminal operator at a FIXED lower endpoint `s`, extended by zero below `s` (o73 (13.1)–(13.2) with
the pin above the clock), with a countable family and absolutely summable coefficients. -/
theorem termKink_sum {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Countable ι] (s : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (h : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (h i)) → (∀ i, timeFourierNorm θ (h i) < ⊤) →
      (∑' i, ‖c i‖ₑ * timeFourierNorm θ (h i)) < ⊤ →
      ∃ g : (Fin 1 → ℝ) → ℂ,
        (∀ T : Fin 1 → ℝ, |T 0 - s| ≤ 1 →
          g T = ∑' i, c i * ∫ u in Set.Ioo s (T 0),
            Complex.exp (((Real.pi * A i * (u - s) : ℝ) : ℂ) * Complex.I) * h i ![T 0, u]) ∧
        timeFourierNorm θ g ≤ ENNReal.ofReal C * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (h i) := by
  have hB := Bk_nonneg
  refine ⟨2 ^ θ * Bk, by positivity, ?_⟩
  intro ι _ s A c h hc hfin hsum
  let _ : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hi : ∀ i, Integrable (h i) := fun i => integrable_of_timeFourierNorm_lt_top (hfin i)
  have hhat : ∀ i, Integrable (timeFourier (h i)) :=
    fun i => integrable_timeFourier_of_norm_lt_top hθ0 (hfin i)
  have hhc : ∀ i, Continuous (timeFourier (h i)) := fun i => timeFourier_continuous (hi i)
  let F : ι → (Fin 1 → ℝ) → ℂ := fun i T => c i * Gsyn (A i) s (h i) T
  have hFm : ∀ i, Measurable (F i) := fun i => measurable_const.mul (Gsyn_measurable (A i) s (hhc i))
  have hFi : ∀ i, Integrable (F i) := fun i => (Gsyn_integrable (A i) s (hhat i) (hhc i)).const_mul (c i)
  have hM1 : ∫⁻ T, ENNReal.ofReal (mk s T) < ⊤ := (mk_integrable s).lintegral_lt_top
  have hmass : (∑' i, ∫⁻ T, ‖F i T‖ₑ) < ⊤ := by
    calc (∑' i, ∫⁻ T, ‖F i T‖ₑ)
        ≤ ∑' i, (∫⁻ T, ENNReal.ofReal (mk s T)) * (‖c i‖ₑ * timeFourierNorm θ (h i)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          simp only [F, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
          calc ‖c i‖ₑ * ∫⁻ T, ‖Gsyn (A i) s (h i) T‖ₑ
              ≤ ‖c i‖ₑ * ((∫⁻ l, ‖timeFourier (h i) l‖ₑ) * ∫⁻ T, ENNReal.ofReal (mk s T)) := by
                gcongr
                exact lintegral_Gsyn_le (A i) s (h i)
            _ ≤ ‖c i‖ₑ * (timeFourierNorm θ (h i) * ∫⁻ T, ENNReal.ofReal (mk s T)) := by
                gcongr
                exact lintegral_enorm_le_norm hθ0 (hi i)
            _ = _ := by ring
      _ = (∫⁻ T, ENNReal.ofReal (mk s T)) * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (h i) :=
          ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top hM1 hsum
  have hsumT : ∀ T, Summable (fun i => ‖F i T‖) := by
    intro T
    have hle : (∑' i, ‖F i T‖ₑ) ≤ 2 * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (h i) := by
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun i => ?_
      simp only [F, enorm_mul]
      calc ‖c i‖ₑ * ‖Gsyn (A i) s (h i) T‖ₑ ≤ ‖c i‖ₑ * (2 * timeFourierNorm θ (h i)) := by
            gcongr
            exact (enorm_Gsyn_le (A i) s (h i) T).trans (by gcongr; exact lintegral_enorm_le_norm hθ0 (hi i))
        _ = _ := by ring
    have hne : (∑' i, ‖F i T‖ₑ) ≠ ⊤ := (hle.trans_lt (ENNReal.mul_lt_top (by norm_num) hsum)).ne
    simpa only [toReal_enorm] using ENNReal.summable_toReal hne
  refine ⟨fun T => ∑' i, F i T, fun T hT => ?_, ?_⟩
  · show ∑' i, F i T = _
    refine tsum_congr fun i => ?_
    simp only [F]
    rw [op_eq_synth (A i) s (hc i) (hi i) (hhat i) T hT]
  · have hg : (fun T => ∑' i, F i T) = fun T => ∫ i, F i T ∂Measure.count := by
      funext T
      exact (Sumint.count_integral_eq_tsum (fun i => F i T) (hsumT T)).symm
    rw [hg]
    refine (timeFourierNorm_count_le θ F hFm hFi hmass).trans ?_
    calc ∑' i, timeFourierNorm θ (F i)
        ≤ ∑' i, ENNReal.ofReal (2 ^ θ * Bk) * (‖c i‖ₑ * timeFourierNorm θ (h i)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have e : F i = fun T => c i • Gsyn (A i) s (h i) T := rfl
          rw [e, timeFourierNorm_smul]
          calc ‖c i‖ₑ * timeFourierNorm θ (Gsyn (A i) s (h i))
              ≤ ‖c i‖ₑ * (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal Bk * timeFourierNorm θ (h i)) := by
                gcongr
                exact Gsyn_norm_le hθ0 hθ1 (A i) s (hfin i)
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity)]
                ring
      _ = _ := ENNReal.tsum_mul_left

end WaveTurbulence.Flower.ProtPin
