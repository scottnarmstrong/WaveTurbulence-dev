/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedInverseMatrix
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedPredecessorSystem
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedInverseMatrix
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedPredecessorSystem` (sha256 72ce75bd7982b7e6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Complete frozen predecessor hypotheses for normalized source matrices -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem normalized_matrix_predecessor_coeffΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v j : (assemblyShapeΓ hM9 B).VIdx) :
    normalizedBranchMatrixΓ hM9 B v j -
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => normalizedBranchMatrixΓ hM9 B u j) =
      ∑ p, assemblyCoeffΓ hM9 B hG v (.inl p)*normalizedPairMatrixΓ hM9 B hG p j := by
  have he := congrArg (fun z : ℤ => z*jointFlipSign (assemblyShapeΓ hM9 B) j)
    (assembly_matrix_predecessor_coeffΓ hM9 B hG v j)
  cases hp : assemblyPrevΓ hM9 B v with
  | none =>
    simpa only [normalizedBranchMatrixΓ,normalizedPairMatrixΓ,hp,Option.elim_none,sub_zero,
      Finset.sum_mul,mul_assoc] using he
  | some u =>
    simpa only [normalizedBranchMatrixΓ,normalizedPairMatrixΓ,hp,Option.elim_some,sub_mul,
      Finset.sum_mul,mul_assoc] using he

theorem prod_assemblyBudget_real_leΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    (∏ v, (assemblyBudgetΓ hM9 B v : ℝ)) ≤ (6561 : ℝ)^(assemblyShapeΓ hM9 B).M := by
  exact_mod_cast prod_assemblyBudget_leΓ hM9 B

/-- Every clause of frozen sumint(ii), including coefficient and affine
identities, positivity, true coefficient counts, and the product bound. -/
theorem normalized_predecessor_systemΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    (∀ v, (∀ p, IsUnitCoeff (assemblyCoeffΓ hM9 B hG v (.inl p))) ∧
      (∀ c, IsUnitCoeff (assemblyCoeffΓ hM9 B hG v (.inr c))) ∧
      ((Finset.univ.filter fun p => assemblyCoeffΓ hM9 B hG v (.inl p) ≠ 0).card +
        (Finset.univ.filter fun c => assemblyCoeffΓ hM9 B hG v (.inr c) ≠ 0).card ≤ assemblyBudgetΓ hM9 B v) ∧
      (∀ u, assemblyPrevΓ hM9 B v = some u → (assemblyShapeΓ hM9 B).LexLt u v) ∧
      (∀ j, normalizedBranchMatrixΓ hM9 B v j-(assemblyPrevΓ hM9 B v).elim 0 (fun u => normalizedBranchMatrixΓ hM9 B u j) =
        ∑ p, assemblyCoeffΓ hM9 B hG v (.inl p)*normalizedPairMatrixΓ hM9 B hG p j) ∧
      (∀ c, assemblyBranchBoundaryRowΓ hM9 B v c-(assemblyPrevΓ hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRowΓ hM9 B u c) =
        (∑ p, assemblyCoeffΓ hM9 B hG v (.inl p)*assemblyPairBoundaryRowΓ hM9 B hG p c)+assemblyCoeffΓ hM9 B hG v (.inr c))) ∧
    (∀ v, 1 ≤ assemblyBudgetΓ hM9 B v) ∧
      ((∏ v, (assemblyBudgetΓ hM9 B v : ℝ)) ≤ (6561 : ℝ)^(assemblyShapeΓ hM9 B).M) := by
  classical
  refine ⟨?_,assemblyBudget_posΓ hM9 B,prod_assemblyBudget_real_leΓ hM9 B⟩
  intro v
  exact ⟨fun p => assemblyCoeff_unitΓ hM9 B hG v (.inl p),
    fun c => assemblyCoeff_unitΓ hM9 B hG v (.inr c),assemblyCoeff_count_leΓ hM9 B hG v,
    fun u hu => assemblyPrev_ltΓ hM9 B v u hu,normalized_matrix_predecessor_coeffΓ hM9 B hG v,
    assembly_boundary_predecessor_coeffΓ hM9 B hG v⟩

end WaveTurbulence.GammaLow.Famb.VineEstS2
