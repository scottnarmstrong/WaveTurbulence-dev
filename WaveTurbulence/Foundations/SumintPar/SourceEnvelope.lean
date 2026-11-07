/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTotalCoefficientMass
public import WaveTurbulence.Foundations.SumintPar.NormalizedSourceCoefficient
public import WaveTurbulence.Foundations.SumintPar.CellEnvelope
import Mathlib.Tactic

/-!
# The `r`-free majorant of the source Fourier coefficient

With the `𝒦` weights allowed to depend on `r = e - f`, the source Fourier coefficient depends on
`r`. Its pointwise (in the frequency) norm is dominated by an `r`-free function `coefMajor`, whose
total mass over the localization labels obeys the same bound as the mass of a single coefficient.
This is what lets the output-supremum inside `XNorm00` pass through the frequency integral.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.SumintPar

/-- The decay budget of the `𝒦` weight at index `v`. -/
@[expose] noncomputable def weightBudget {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) (v : D.S.VIdx) : ℝ :=
  L ^ (-(gammaWeight d γ - Real.sqrt η) * (D.g v : ℝ))

theorem weightBudget_nonneg {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (v : D.S.VIdx) : 0 ≤ weightBudget D L γ η v := Real.rpow_nonneg hL.le _

/-- The `r`-free majorant of `‖sourceCoefficient D a b r ξ‖`. -/
@[expose] noncomputable def coefMajor {d : ℕ} (D : SumintDatum d) (L γ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) : ℝ :=
  (∏ v, cellEnv d D.wDec (weightBudget D L γ η v) (a v) (ξ (.inl v))) *
    ∏ v, ‖𝓕 (localizedWeight (b v) (D.wL v)) (ξ (.inr v))‖

theorem coefMajor_nonneg {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) :
    0 ≤ coefMajor D L γ η a b ξ :=
  mul_nonneg (Finset.prod_nonneg fun v _ => cellEnv_nonneg _ _ (weightBudget_nonneg D hL γ η v) _ _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem norm_sourceCoefficient_le_coefMajor {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) :
    ‖sourceCoefficient D a b r ξ‖ ≤ coefMajor D L γ η a b ξ := by
  unfold sourceCoefficient coefMajor
  rw [norm_prod, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, sourceWeight]
  have hK : ∏ v, ‖𝓕 (localizedWeight (a v) (D.wK v r)) (ξ (.inl v))‖ ≤
      ∏ v, cellEnv d D.wDec (weightBudget D L γ η v) (a v) (ξ (.inl v)) := by
    apply Finset.prod_le_prod₀ (fun v _ => norm_nonneg _)
    intro v _
    exact norm_fourier_localizedWeight_le_cellEnv hD.wN_ne_zero hD.reg.1
      (weightBudget_nonneg D hL γ η v) ((hD.2.2.2.2.1 v).1 r) (a v) _
  exact mul_le_mul_of_nonneg_right hK (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem integral_coefMajor {d : ℕ} (D : SumintDatum d) (L γ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∫ ξ, coefMajor D L γ η a b ξ =
      (∏ v, cellOmega d D.wDec (weightBudget D L γ η v) (a v)) *
        ∏ v, ∫ ξ : Mom d, ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖ := by
  have h := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : D.S.VIdx ⊕ D.S.VIdx => Mom d)
    (fun i ξ => Sum.elim (fun v => cellEnv d D.wDec (weightBudget D L γ η v) (a v) ξ)
      (fun v => ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖) i)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  unfold coefMajor
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  exact integral_cellEnv _ _ _ _

/-- Primary label sum of the cell envelope masses. -/
theorem tsum_primary_cellOmega_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∏ v, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) (a v))) ≤
      ENNReal.ofReal (summedCellFourierFactor d (d+1)^D.S.M *
        ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))) := by
  have hB (v : D.S.VIdx) : 0 ≤ weightBudget D L γ η v := weightBudget_nonneg D hL γ η v
  have hsingle (v : D.S.VIdx) :
      (∑' a : Fin d → ℤ, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) a)) ≤
        ENNReal.ofReal (summedCellFourierFactor d (d+1) * weightBudget D L γ η v) :=
    tsum_ofReal_cellOmega_le_base hD.reg.2 (hB v)
  calc
    _ ≤ ∏ v, ∑' a : Fin d → ℤ, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) a) :=
      tsum_product_le_product_tsum _
    _ ≤ ∏ v, ENNReal.ofReal (summedCellFourierFactor d (d+1) * weightBudget D L γ η v) :=
      Finset.prod_le_prod (fun v _ => hsingle v)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg
        (fun v _ => mul_nonneg (summedCellFourierFactor_nonneg _ _) (hB v))]
      congr 1
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,card_vector_index]
      rfl

/-- Sum the alternative cell coefficient majorants using only the fixed-family count. -/
theorem sum_alternative_coefMajor_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx → Fin d → ℤ) :
    (∑ b ∈ sourceAlternativeLabels D hD a, ENNReal.ofReal (∫ ξ, coefMajor D L γ η a b ξ)) ≤
      ENNReal.ofReal (((9:ℝ)^d*A^d)^D.S.M) *
        (∏ v, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) (a v))) *
        ENNReal.ofReal (cellFourierFactor d^D.S.M *
          ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))) := by
  let P := ∏ v, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) (a v))
  let Q := ENNReal.ofReal (cellFourierFactor d^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ)))
  have hc : ((sourceAlternativeLabels D hD a).card : ℝ≥0∞) ≤
      ENNReal.ofReal (((9:ℝ)^d*A^d)^D.S.M) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (card_sourceAlternativeLabels_le D hD a)
  have hΩ (v : D.S.VIdx) : 0 ≤ cellOmega d D.wDec (weightBudget D L γ η v) (a v) := by
    unfold cellOmega
    exact mul_nonneg (Fourier.fourierL1Constant_nonneg _)
      (Finset.sum_nonneg fun j _ => integral_nonneg
        (derivMajorant_nonneg _ _ _ (weightBudget_nonneg D hL γ η v) _))
  calc
    _ ≤ ∑ _b ∈ sourceAlternativeLabels D hD a, P*Q := by
      apply Finset.sum_le_sum
      intro b _
      rw [integral_coefMajor, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hΩ v),
        ENNReal.ofReal_prod_of_nonneg (fun v _ => hΩ v),
        ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))]
      exact mul_le_mul' le_rfl (alternative_fourier_mass_le hd D hL hD b)
    _ = ((sourceAlternativeLabels D hD a).card : ℝ≥0∞)*P*Q := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl

/-- **Total mass of the `r`-free coefficient majorants**, with the same constant as for one `r`. -/
theorem tsum_coefMajor_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∑ b ∈ sourceAlternativeLabels D hD a, ENNReal.ofReal (∫ ξ, coefMajor D L γ η a b ξ)) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M *
        L^(-(gammaWeight d γ-Real.sqrt η)*D.M₁)) := by
  let P := fun a : D.S.VIdx → Fin d → ℤ =>
    ∏ v, ENNReal.ofReal (cellOmega d D.wDec (weightBudget D L γ η v) (a v))
  let U := ((9:ℝ)^d*A^d)^D.S.M
  let V := cellFourierFactor d^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))
  let W := summedCellFourierFactor d (d+1)^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))
  have hU : 0 ≤ U := pow_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hA) _)) _
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg (summedCellFourierFactor_nonneg _ _) _)
    (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hL.le _))
  calc
    _ ≤ ∑' a, ENNReal.ofReal U*P a*ENNReal.ofReal V :=
      ENNReal.tsum_le_tsum (fun a => sum_alternative_coefMajor_mass_le hd D hL hD a)
    _ = ENNReal.ofReal U*(∑' a, P a)*ENNReal.ofReal V := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal U*ENNReal.ofReal W*ENNReal.ofReal V :=
      mul_le_mul' (mul_le_mul' le_rfl (tsum_primary_cellOmega_le D hL hD)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul hU,← ENNReal.ofReal_mul (mul_nonneg hU hW)]
      congr 1
      dsimp [U,V,W]
      have he := prod_primary_alternative_decay D hL (gammaWeight d γ-Real.sqrt η)
      calc
        _ = (((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M *
            ((∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))) *
              ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))) := by
          simp only [mul_pow]
          ring
        _ = _ := by rw [he]

theorem continuous_fourier_wL {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (b : D.S.VIdx → Fin d → ℤ) (v : D.S.VIdx) :
    Continuous (𝓕 (localizedWeight (b v) (D.wL v))) := by
  have hf := contDiff_of_SNorm_le hD.wN_ne_zero ((hD.2.2.2.2.1 v).2)
  have hi : Integrable (localizedWeight (b v) (D.wL v)) :=
    (localizedWeight_contDiff _ hf).continuous.integrable_of_hasCompactSupport
      (localizedWeight_hasCompactSupport _ _)
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi

theorem continuous_coefMajor {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) : Continuous (coefMajor D L γ η a b) := by
  unfold coefMajor
  apply Continuous.mul
  · apply continuous_finsetProd
    intro v _
    exact (continuous_cellEnv _ _ _ _).comp (continuous_apply _)
  · apply continuous_finsetProd
    intro v _
    exact (continuous_fourier_wL D hD b v).norm.comp (continuous_apply _)

theorem integrable_coefMajor {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) : Integrable (coefMajor D L γ η a b) := by
  have h := Integrable.fintype_prod (μ := fun _ : D.S.VIdx ⊕ D.S.VIdx => (volume : Measure (Mom d)))
    (f := fun (i : D.S.VIdx ⊕ D.S.VIdx) (ξ : Mom d) => Sum.elim
      (fun v => cellEnv d D.wDec (weightBudget D L γ η v) (a v) ξ)
      (fun v => ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖) i)
    (fun i => by
      cases i with
      | inl v => exact integrable_cellEnv _ _ _ _
      | inr v =>
        exact (localizedWeight_fourier_integrable_and_bound hD.wN_ne_zero hD.reg.1
          (Real.rpow_nonneg hL.le _) ((hD.2.2.2.2.1 v).2) (b v)).1.norm)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  exact h

/-- The normalized majorant masses, with the constant of the single-`r` estimate. -/
theorem tsum_normalizedCoefMajor_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) :
    (∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
      ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ)) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M) := by
  have hW := sourceWeightDecay_pos D hL γ η
  simp_rw [integral_const_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hW.le), ← Finset.mul_sum]
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (tsum_coefMajor_mass_le hd D hA hL hD)).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hW.le)]
  congr 1
  change (sourceWeightDecay D L γ η)⁻¹*(_*sourceWeightDecay D L γ η) = _
  rw [mul_left_comm,inv_mul_cancel₀ hW.ne',mul_one]

end WaveTurbulence.SumintPar
