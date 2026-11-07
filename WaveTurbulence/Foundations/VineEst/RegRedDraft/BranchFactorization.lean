/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.BranchCoordinateSplit
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Exact product, sum and integral identities in the actual source clock partition -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem prod_sourceBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {M : Type*} [CommMonoid M] (f : GBranch (D.forest hS) → M) :
    (∏ b, f b) = (∏ b : GBranch S.tree, f (D.coreBranch hS b)) *
      (∏ p : SourcePair S, ∏ b : GBranch (decodedCouple (D.couple p)).tree, f (coupleContextBranch D hS p b)) *
      (∏ b : GBranch S.tree, ∏ q : ChainBranchPath D b, f (chainContextBranch D hS b q)) := by
  rw [← (sourceBranchEquiv D hS).prod_comp f,Fintype.prod_sum_type,Fintype.prod_sum_type,
    Fintype.prod_sigma,Fintype.prod_sigma]
  simp only [sourceBranchEquiv_core,sourceBranchEquiv_couple,sourceBranchEquiv_chain,mul_assoc]

theorem sum_sourceBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {M : Type*} [AddCommMonoid M] (f : GBranch (D.forest hS) → M) :
    (∑ b, f b) = (∑ b : GBranch S.tree, f (D.coreBranch hS b)) +
      (∑ p : SourcePair S, ∑ b : GBranch (decodedCouple (D.couple p)).tree, f (coupleContextBranch D hS p b)) +
      (∑ b : GBranch S.tree, ∑ q : ChainBranchPath D b, f (chainContextBranch D hS b q)) := by
  rw [← (sourceBranchEquiv D hS).sum_comp f,Fintype.sum_sum_type,Fintype.sum_sum_type,
    Fintype.sum_sigma,Fintype.sum_sigma]
  simp only [sourceBranchEquiv_core,sourceBranchEquiv_couple,sourceBranchEquiv_chain,add_assoc]

/-- Conditional Fubini helper. Integrability of the actual source kernel
integrand is supplied by KernelIntegrand/KernelFubini, not assumed by redkg. -/
theorem integral_sourceTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (f : (GBranch (D.forest hS) → ℝ) → ℂ) (hf : Integrable f) :
    (∫ τ, f τ) = ∫ τcore, ∫ τreplacement, f ((sourceTimeSplit D hS).symm (τcore,τreplacement)) := by
  have hmp := measurePreserving_sourceTimeSplit D hS
  have hi := hmp.symm.integrable_comp_of_integrable hf
  exact (hmp.symm.integral_comp' f).symm.trans (integral_prod _ hi)

end WaveTurbulence.RegRed
