/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestRootTimes
public import WaveTurbulence.Foundations.XChain.ForestPhaseIntegral
public import WaveTurbulence.Foundations.XChain.SignedIntegrals
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! The signed forest phase product is the product of its signed single-tree phase products. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

theorem single_branch_phase_eq {w d : ℕ} (L γ δ : ℝ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (κ : GNode top → (Fin d → ℤ)) (τ : GBranch top → ℝ)
    (j : Fin w) (b : GBranch (single (top j))) :
    Complex.exp ((Real.pi * ((nodeSign sig (singleBranchToForest top j b).toNode.1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      resFactor (latticePoint L (κ ((singleBranchToForest top j b).child 0)))
        (latticePoint L (κ ((singleBranchToForest top j b).child 1)))
        (latticePoint L (κ ((singleBranchToForest top j b).child 2)))
        (latticePoint L (κ (singleBranchToForest top j b).toNode)) * τ (singleBranchToForest top j b) : ℝ) * Complex.I) =
    zpowSign (sig j) (Complex.exp ((Real.pi * ((treeSign (top j) b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      resFactor (latticePoint L (κ (singleNodeToForest top j (b.child 0))))
        (latticePoint L (κ (singleNodeToForest top j (b.child 1))))
        (latticePoint L (κ (singleNodeToForest top j (b.child 2))))
        (latticePoint L (κ (singleNodeToForest top j b.toNode))) * τ (singleBranchToForest top j b) : ℝ) * Complex.I)) := by
  rw [zpowSign_exp_real_mul_I]
  have hs := congrArg (fun z : ℤˣ => ((z : ℤ) : ℝ)) (nodeSign_single_mul sig top j b.toNode)
  simp only [Units.val_mul, Int.cast_mul] at hs
  apply congrArg (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
  have he := congrArg (fun z : ℝ => Real.pi * z * δ * L ^ (2 * γ) *
    resFactor (latticePoint L (κ (singleNodeToForest top j (b.child 0))))
      (latticePoint L (κ (singleNodeToForest top j (b.child 1))))
      (latticePoint L (κ (singleNodeToForest top j (b.child 2))))
      (latticePoint L (κ (singleNodeToForest top j b.toNode))) * τ (singleBranchToForest top j b)) hs.symm
  exact he.trans (by ring)

theorem forestPhaseProd_eq_roots {w d : ℕ} (L γ δ : ℝ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (κ : GNode top → (Fin d → ℤ)) (τ : GBranch top → ℝ) :
    forestPhaseProd L γ δ sig top (fun a => latticePoint L (κ a)) τ =
      ∏ j, zpowSign (sig j) (phaseFn L γ δ (top j)
        (fun a => κ (singleNodeToForest top j a)) (fun b => τ (singleBranchToForest top j b))) := by
  unfold forestPhaseProd
  have he := Fintype.prod_equiv (forestSingleBranchEquiv top)
    (fun b : GBranch top => Complex.exp ((Real.pi * ((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      resFactor (latticePoint L (κ (b.child 0))) (latticePoint L (κ (b.child 1)))
        (latticePoint L (κ (b.child 2))) (latticePoint L (κ b.toNode)) * τ b : ℝ) * Complex.I))
    (fun z : Σ j : Fin w, GBranch (single (top j)) =>
      zpowSign (sig z.1) (Complex.exp ((Real.pi * ((treeSign (top z.1) z.2.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        resFactor (latticePoint L (κ (singleNodeToForest top z.1 (z.2.child 0))))
          (latticePoint L (κ (singleNodeToForest top z.1 (z.2.child 1))))
          (latticePoint L (κ (singleNodeToForest top z.1 (z.2.child 2))))
          (latticePoint L (κ (singleNodeToForest top z.1 z.2.toNode))) * τ (singleBranchToForest top z.1 z.2) : ℝ) * Complex.I)))
    (fun b => single_branch_phase_eq L γ δ top sig κ τ b.1.1 ⟨(0, b.1.2), b.2⟩)
  rw [he, Fintype.prod_sigma]
  exact prod_congr rfl (fun j _ => (zpowSign_prod (sig j) univ _).symm)

end WaveTurbulence.Induct
