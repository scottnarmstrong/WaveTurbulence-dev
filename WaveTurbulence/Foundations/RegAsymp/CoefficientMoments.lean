/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.MomentWeights

/-! # From J3 per-variable moments to the NT maximum moment

DH23 (maincoef2.5) to (propertypsi2). The author's J3 API bounds each
variable separately. Summing costs only the number of remaining variables,
not a factorial or a power depending exponentially on that number.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR Finset
open scoped ENNReal

/-- J3's literal per-variable estimate bounds the full maximum moment
with the explicit linear loss card(iota). -/
theorem coefficient_max_moment_le {ι : Type} [Fintype ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {a b N : ℝ} (hb : 0 ≤ b)
    (hper : ∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam * (1+‖α i‖ₑ)^b * ‖C α lam‖ₑ ≤ ENNReal.ofReal N) :
    ∫⁻ α, ∫⁻ lam, wL a lam * ENNReal.ofReal (ApproxNT.wmax b α) * ‖C α lam‖ₑ ≤
      Fintype.card ι * ENNReal.ofReal N := by
  classical
  let H : ι → (ι → ℝ) → (ℝ × ℝ) → ℝ≥0∞ :=
    fun i α lam => wL a lam * (1+‖α i‖ₑ)^b * ‖C α lam‖ₑ
  change ∀ i, (∫⁻ α, ∫⁻ lam, H i α lam) ≤ ENNReal.ofReal N at hper
  have hm (i : ι) : Measurable (Function.uncurry (H i)) :=
    (((measurable_wL a).comp measurable_snd).mul (by fun_prop)).mul hC.meas.measurable.enorm
  have hi (α : ι → ℝ) :
      (∫⁻ lam, ∑ i, H i α lam) = ∑ i, ∫⁻ lam, H i α lam :=
    lintegral_finsetSum univ (fun i _ => (hm i).of_uncurry_left)
  have ho : (∫⁻ α, ∑ i, ∫⁻ lam, H i α lam) = ∑ i, ∫⁻ α, ∫⁻ lam, H i α lam :=
    lintegral_finsetSum univ (fun i _ => (hm i).lintegral_prod_right)
  calc
    _ ≤ ∫⁻ α, ∫⁻ lam, ∑ i, H i α lam := by
      apply lintegral_mono
      intro α
      apply lintegral_mono
      intro lam
      dsimp only
      have h := mul_le_mul_left (mul_le_mul_right (ofReal_wmax_le_sum hb α) (wL a lam)) ‖C α lam‖ₑ
      simpa only [H,mul_sum,sum_mul] using h
    _ = ∫⁻ α, ∑ i, ∫⁻ lam, H i α lam := lintegral_congr hi
    _ = ∑ i, ∫⁻ α, ∫⁻ lam, H i α lam := ho
    _ ≤ ∑ _i : ι, ENNReal.ofReal N := sum_le_sum (fun i _ => hper i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

end WaveTurbulence.RegAsymp
