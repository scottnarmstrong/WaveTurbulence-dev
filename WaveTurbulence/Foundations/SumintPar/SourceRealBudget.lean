/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoefficientAssembly
public import WaveTurbulence.Foundations.SumintPar.SourceExponentAssembly
public import WaveTurbulence.Foundations.SumintPar.CellMultiplierBound
public import WaveTurbulence.Foundations.SumintPar.ParameterBound

/-!
# Final real coefficient and exponent budget

The only step-dependent scalar is the compact cell multiplier constant.
It is absorbed using half the eta seventh-power allowance in the
large-L threshold, leaving the fixed constant independent of delta and N.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.SumintPar

/-- The actual interpolated kernel exponent before time restoration. -/
@[expose] noncomputable def sourceKernelExponent {d : ℕ} (D : SumintDatum d) (γ η : ℝ) : ℝ :=
  (D.S.M:ℝ)*((d:ℝ)-γ)-
    (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
    (1-interpolationWeight η)*(partitionExponent η/20)*(D.M₀:ℝ)+14*(d:ℝ)*interpolationWeight η

/-- The exact exponent printed in the drafted source conclusion. -/
@[expose] noncomputable def sourceTargetExponent {d : ℕ} (D : SumintDatum d) (γ η : ℝ) : ℝ :=
  (D.S.M:ℝ)*((d:ℝ)-γ)-
    η^2*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
    η^8*(D.M₀:ℝ)+η^7

/-- The complete real restoration budget fits exactly the drafted coefficient and exponent. -/
theorem source_real_budget_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {A G L γ δ η : ℝ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hL : 1 ≤ L) (hδ : 0 < δ)
    (hη : SumintSmallness d γ η) (N : ℕ)
    (hstep : cellMultiplierRealConstant N*((N:ℝ)+5) ≤ L^(η^7/2)) :
    sourceCoefficientBase d A^D.S.M * 2^(2*η^8) *
      (((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8) * 4^(2*η^8) *
      (cellMultiplierRealConstant N*((N:ℝ)+5)*(L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
      (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(sourceKernelExponent D γ η)) ≤
    sourceAssemblyConstant d A G * parameterMaximum D^(η^6) *
      (sourceAssemblyConstant d A G*δ^(-(1:ℝ)/2))^D.S.M * L^(sourceTargetExponent D γ η) := by
  let S := sourceCoefficientBase d A
  let C := sourceAssemblyConstant d A G
  let P := parameterMaximum D
  let β := partitionExponent η
  let E := sourceKernelExponent D γ η
  have hS : 0 ≤ S := sourceCoefficientBase_nonneg d hA
  have hC : 1 ≤ C := one_le_sourceAssemblyConstant _ _ _
  have hP : 1 ≤ P := one_le_parameterMaximum D hI
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hcell : 0 < cellMultiplierRealConstant N := zero_lt_one.trans_le (one_le_cellMultiplierRealConstant N)
  have hθ : 2*η^8 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity,by linarith only [hη.eight_lt]⟩
  have hbase : 2*S*G ≤ C := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right 1 S) (by norm_num))
      (zero_le_one.trans hG)).trans (le_max_right _ _)
  have hcoeff := source_coefficient_modulation_budget hS hG hP hθ hη.parameter_power D.S.M
    (show 8 ≤ C from le_max_left _ _) hbase
  have hscale : (L^(-β))⁻¹*(L^(-β))⁻¹ = L^(2*β) := by
    rw [← Real.rpow_neg hLp.le,neg_neg,← Real.rpow_add hLp]
    congr 1
    ring
  have hdelta : δ^(-(D.S.M:ℝ)/2) = (δ^(-(1:ℝ)/2))^D.S.M := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  have hexp : E+2*β+η^7/2 ≤ sourceTargetExponent D γ η := source_restored_exponent_le D hη
  have hpower : L^(η^7/2)*L^(E+2*β) ≤ L^(sourceTargetExponent D γ η) := by
    rw [← Real.rpow_add hLp]
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith only [hexp]
  change S^D.S.M*2^(2*η^8)*(((D.S.M:ℝ)+1)*P)^(2*η^8)*4^(2*η^8)*
    (cellMultiplierRealConstant N*((N:ℝ)+5)*(L^(-β))⁻¹*(L^(-β))⁻¹)*
    (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^E) ≤ _
  calc
    _ = (S^D.S.M*2^(2*η^8)*(((D.S.M:ℝ)+1)*P)^(2*η^8)*4^(2*η^8)*G^D.S.M)*
        δ^(-(D.S.M:ℝ)/2)*(cellMultiplierRealConstant N*((N:ℝ)+5))*L^(E+2*β) := by
      rw [mul_assoc (cellMultiplierRealConstant N*((N:ℝ)+5)),hscale,Real.rpow_add hLp]
      ring
    _ ≤ (C*P^(η^6)*C^D.S.M)*δ^(-(D.S.M:ℝ)/2)*L^(η^7/2)*L^(E+2*β) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
      · exact hstep
      · positivity
      · positivity
    _ ≤ (C*P^(η^6)*C^D.S.M)*δ^(-(D.S.M:ℝ)/2)*L^(sourceTargetExponent D γ η) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by rw [hdelta,mul_pow]; ring

end WaveTurbulence.SumintPar
