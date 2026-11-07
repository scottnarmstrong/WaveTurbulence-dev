/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceRestrictionInterpolated
public import WaveTurbulence.Foundations.SumintPar.SourceRealBudget
public import WaveTurbulence.Foundations.SumintPar.StrictPowerAbsorption

/-!
# The full source sumint bound with the correct fixed-constant dependence

The fixed C1 is chosen before delta and the step count. Only the large-L
threshold absorbs the compact restoration multiplier, using the reserved
half eta seventh-power loss. No size restriction is needed for this
stronger intermediate estimate.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- TARGET sumint: the exact restriction estimate, with C1 independent of delta and the step count. -/
theorem exists_source_sumint_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0:ℝ) 1)
    (η : ℝ) (hη : SumintSmallness d γ η) (A : ℝ) (hA : 1 ≤ A)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintDatum d) (hI : 0 < D.S.I),
      D.Admissible A L γ η N →
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => D.expr hI L γ δ η t v) ≤
      ENNReal.ofReal (C1*parameterMaximum D^(η^6)*(C1*δ^(-(1:ℝ)/2))^D.S.M*
        L^(sourceTargetExponent D γ η)) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_restriction_interpolated_bound d hd γ hγ η hη τstar hτstar
  let C1 := sourceAssemblyConstant d A G
  refine ⟨C1,one_le_sourceAssemblyConstant _ _ _,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  have hηpos := hη.eta_pos
  obtain ⟨Rstep,hRstep,hstep⟩ := exists_constant_le_rpow
    (cellMultiplierRealConstant N*((N:ℝ)+5)) (show 0 < η^7/2 by positivity)
  refine ⟨max R Rstep,hR.trans (le_max_left _ _),?_⟩
  intro L hL D hI hD
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLS : Rstep ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hR,hLR]
  have hL1 : 1 ≤ L := by linarith only [hR,hLR]
  have hS : 0 ≤ sourceCoefficientBase d A := sourceCoefficientBase_nonneg d hA
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hP : 0 < parameterMaximum D := zero_lt_one.trans_le (one_le_parameterMaximum D hI)
  have hcell : 0 < cellMultiplierRealConstant N := zero_lt_one.trans_le (one_le_cellMultiplierRealConstant N)
  apply (hbound L hLR D hI A hA hD).trans
  have hbudget := source_real_budget_le D hI hA hG hL1 hδ.1 hη N (hstep L hLS)
  change ENNReal.ofReal (sourceCoefficientBase d A^D.S.M)*
    (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
      (ENNReal.ofReal (4^(2*η^8))*
        (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
          (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
          ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(sourceKernelExponent D γ η))))) ≤ _
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  convert hbudget using 1; ring

end WaveTurbulence.SumintPar
