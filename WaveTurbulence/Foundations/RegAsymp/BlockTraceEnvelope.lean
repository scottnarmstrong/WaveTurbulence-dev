/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockTraceIntegral
public import WaveTurbulence.Foundations.RegAsymp.ShiftedCoefficientEnvelope
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer

/-! # Common all-orders envelope for simultaneous Wick energy traces -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- Freezing an entire block preserves the literal source qualitative regularity. -/
theorem symReg_blockTraceSymbol {ι κ : Type} [Fintype ι] [Fintype κ]
    {C : (ι ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) : SymReg (blockTraceSymbol C) where
  smooth lam := (hC.smooth lam).comp (by
    apply contDiff_pi.mpr
    intro i
    cases i <;> fun_prop [Sum.elim])
  meas := by
    have hm : Measurable (fun p : (κ → ℝ) × (ℝ × ℝ) => (Sum.elim (0 : ι → ℝ) p.1,p.2)) := by
      apply Measurable.prodMk _ measurable_snd
      apply measurable_pi_iff.mpr
      intro i
      cases i <;> fun_prop [Sum.elim]
    exact hC.meas.comp_measurable hm
  dom k := by
    apply ne_top_of_le_ne_top (hC.dom k)
    apply lintegral_mono
    intro lam
    apply iSup_le
    intro β
    exact (dnorm_blockTraceSymbol_le (hC.smooth lam) k β).trans (dnorm_le_supD k C _ lam)

private theorem tsum_finsetSum_ennreal {I : Type*} (S : Finset I) (f : ℕ → I → ℝ≥0∞) :
    (∑' k : ℕ, ∑ j ∈ S, f k j) = ∑ j ∈ S, ∑' k : ℕ, f k j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,ENNReal.tsum_add,ih]

/-- Every all-orders block trace is paid by finitely many source derivative shifts. -/
theorem derivativeCoefficientEnvelope_blockTrace_le {r : ℕ} {κ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) (lam : ℝ × ℝ) :
    derivativeCoefficientEnvelope (blockTraceSymbol C) lam ≤ (2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*shiftedDerivativeCoefficientEnvelope j C lam := by
  unfold derivativeCoefficientEnvelope shiftedDerivativeCoefficientEnvelope
  calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ))*((2:ℝ≥0∞)^r *
        ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*∫⁻ α, dnorm (k+j) C α lam) :=
      ENNReal.tsum_le_tsum (fun k => mul_le_mul' le_rfl (lintegral_dnorm_blockTraceSymbol_le (hC.smooth lam) k))
    _ = (2:ℝ≥0∞)^r * ∑' k : ℕ, ∑ j ∈ Finset.range (r+1),
        ENNReal.ofReal ((r:ℝ)^j)*(ENNReal.ofReal (1/((4*k).factorial:ℝ))*∫⁻ α, dnorm (k+j) C α lam) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro k
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    _ = _ := by
      rw [tsum_finsetSum_ennreal]
      simp_rw [ENNReal.tsum_mul_left]

/-- The traced envelope preserves finite mass under the original strong temporal weight. -/
theorem derivativeCoefficientEnvelope_blockTrace_mass_lt_top {r : ℕ} {κ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (blockTraceSymbol C) lam) < ⊤ := by
  apply lt_of_le_of_lt (lintegral_mono (fun lam => mul_le_mul' le_rfl
    (derivativeCoefficientEnvelope_blockTrace_le hC lam)))
  have he (lam : ℝ × ℝ) : wL θ lam*((2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*shiftedDerivativeCoefficientEnvelope j C lam) =
      (2:ℝ≥0∞)^r * ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        (wL θ lam*shiftedDerivativeCoefficientEnvelope j C lam) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (by finiteness),lintegral_finsetSum (f := fun j lam =>
    ENNReal.ofReal ((r:ℝ)^j)*(wL θ lam*shiftedDerivativeCoefficientEnvelope j C lam)) _
      (fun j _ => measurable_const.mul ((measurable_wL θ).mul
        (measurable_shiftedDerivativeCoefficientEnvelope j hC)))]
  apply ENNReal.mul_lt_top (by finiteness)
  apply ENNReal.sum_lt_top.mpr
  intro j _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (shiftedDerivativeCoefficientEnvelope_mass_lt_top j hC hN hA hmain)

end WaveTurbulence.RegAsymp
