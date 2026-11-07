/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedInverseMatrix

/-! # Complete frozen predecessor hypotheses for normalized source matrices -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem normalized_matrix_predecessor_coeff (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v j : (assemblyShape hM9 B).VIdx) :
    normalizedBranchMatrix hM9 B v j -
      (assemblyPrev hM9 B v).elim 0 (fun u => normalizedBranchMatrix hM9 B u j) =
      ∑ p, assemblyCoeff hM9 B hG v (.inl p)*normalizedPairMatrix hM9 B hG p j := by
  have he := congrArg (fun z : ℤ => z*jointFlipSign (assemblyShape hM9 B) j)
    (assembly_matrix_predecessor_coeff hM9 B hG v j)
  cases hp : assemblyPrev hM9 B v with
  | none =>
    simpa only [normalizedBranchMatrix,normalizedPairMatrix,hp,Option.elim_none,sub_zero,
      Finset.sum_mul,mul_assoc] using he
  | some u =>
    simpa only [normalizedBranchMatrix,normalizedPairMatrix,hp,Option.elim_some,sub_mul,
      Finset.sum_mul,mul_assoc] using he

theorem prod_assemblyBudget_real_le (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (∏ v, (assemblyBudget hM9 B v : ℝ)) ≤ (6561 : ℝ)^(assemblyShape hM9 B).M := by
  exact_mod_cast prod_assemblyBudget_le hM9 B

/-- Every clause of frozen sumint(ii), including coefficient and affine
identities, positivity, true coefficient counts, and the product bound. -/
theorem normalized_predecessor_system (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    (∀ v, (∀ p, IsUnitCoeff (assemblyCoeff hM9 B hG v (.inl p))) ∧
      (∀ c, IsUnitCoeff (assemblyCoeff hM9 B hG v (.inr c))) ∧
      ((Finset.univ.filter fun p => assemblyCoeff hM9 B hG v (.inl p) ≠ 0).card +
        (Finset.univ.filter fun c => assemblyCoeff hM9 B hG v (.inr c) ≠ 0).card ≤ assemblyBudget hM9 B v) ∧
      (∀ u, assemblyPrev hM9 B v = some u → (assemblyShape hM9 B).LexLt u v) ∧
      (∀ j, normalizedBranchMatrix hM9 B v j-(assemblyPrev hM9 B v).elim 0 (fun u => normalizedBranchMatrix hM9 B u j) =
        ∑ p, assemblyCoeff hM9 B hG v (.inl p)*normalizedPairMatrix hM9 B hG p j) ∧
      (∀ c, assemblyBranchBoundaryRow hM9 B v c-(assemblyPrev hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRow hM9 B u c) =
        (∑ p, assemblyCoeff hM9 B hG v (.inl p)*assemblyPairBoundaryRow hM9 B hG p c)+assemblyCoeff hM9 B hG v (.inr c))) ∧
    (∀ v, 1 ≤ assemblyBudget hM9 B v) ∧
      ((∏ v, (assemblyBudget hM9 B v : ℝ)) ≤ (6561 : ℝ)^(assemblyShape hM9 B).M) := by
  classical
  refine ⟨?_,assemblyBudget_pos hM9 B,prod_assemblyBudget_real_le hM9 B⟩
  intro v
  exact ⟨fun p => assemblyCoeff_unit hM9 B hG v (.inl p),
    fun c => assemblyCoeff_unit hM9 B hG v (.inr c),assemblyCoeff_count_le hM9 B hG v,
    fun u hu => assemblyPrev_lt hM9 B v u hu,normalized_matrix_predecessor_coeff hM9 B hG v,
    assembly_boundary_predecessor_coeff hM9 B hG v⟩

end WaveTurbulence.VineEstS2
