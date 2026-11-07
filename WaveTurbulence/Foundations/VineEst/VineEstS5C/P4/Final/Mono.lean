/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.VineEst.VineEstS3.StepMono
public import WaveTurbulence.Foundations.Vine.DegenVinePar.ScaledSumintMix
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # V5 FINAL: large-constant monotonicity of the parametric `sumint` bound

`sumintMixPar_mono`: the parametric analogue of `VineEstS3.sumintMix_mono` for `SumintMixParDoubledAt` (copy-and-edit; the right-hand side
`sumintRHS` of `VineEstS3Par.Eng` is monotone in `C₁`).  Used to move the prefix statement `SumintMixParDoubled` to the engine parameters
`{P with C₁ := c₀}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Final
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVinePar MeasureTheory Set
open scoped ENNReal

theorem sumintRHSPar_mono (P : WTParams) (D : SumintPar.SumintDatum P.d) {C₁ C₂ : ℝ} (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁)
    (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) :
    sumintRHS P D ≤ sumintRHS {P with C₁ := C₁, C₂ := C₂} D := by
  unfold sumintRHS
  have h1 : 0 ≤ maxPar D ^ (P.η ^ 6) := by
    unfold maxPar
    exact Real.rpow_nonneg (Real.iSup_nonneg fun v => by unfold jbr; positivity) _
  have h2 : 0 ≤ P.δ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hδ _
  have h3 : 0 ≤ P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
      P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) - P.η ^ 8 * D.M₀ + P.η ^ 7) :=
    Real.rpow_nonneg hL _
  have hC' : 0 ≤ C₁ := hC.trans hCC
  have hA : P.C₁ * maxPar D ^ (P.η ^ 6) ≤ C₁ * maxPar D ^ (P.η ^ 6) := mul_le_mul_of_nonneg_right hCC h1
  have hB : (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M ≤ (C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M :=
    pow_le_pow_left₀ (mul_nonneg hC h2) (mul_le_mul_of_nonneg_right hCC h2) _
  exact mul_le_mul (mul_le_mul hA hB (pow_nonneg (mul_nonneg hC h2) _) (mul_nonneg hC' h1)) le_rfl h3
    (mul_nonneg (mul_nonneg hC' h1) (pow_nonneg (mul_nonneg hC' h2) _))

theorem sumintMixPar_mono (A : ℝ) : LargeConstantMonotone (SumintMixParDoubledAt A) := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource D hI hAdm hM M
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have h := hsource D hI hAdm (by simpa using hM) M
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (sumintRHSPar_mono P D hc0 hCC hδ.le hL0) M.mass_nonneg

end WaveTurbulence.VineEstS5C.P4.Final
